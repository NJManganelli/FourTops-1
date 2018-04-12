//////////////////////////////////////////////////////////////////////////////
////     Stand-alone code to train the event-level BDT
////////////////////////////////////////////////////////////////////////////////////
#define _USE_MATH_DEFINES
#include "TStyle.h"
#include "TPaveText.h"
#include "TTree.h"
#include "TNtuple.h"
#include <TMatrixDSym.h>
#include <TMatrixDSymEigen.h>
#include <TVectorD.h>
#include <ctime>

#include <cmath>
#include <fstream>
#include <sstream>
#include <sys/stat.h>
#include <errno.h>
#include "TRandom3.h"
#include "TRandom.h"
#include "TProfile.h"
#include <iostream>
#include <map>
#include <cstdlib>

// user code
#include "TopTreeProducer/interface/TRootRun.h"
#include "TopTreeProducer/interface/TRootEvent.h"
#include "TopTreeAnalysisBase/Selection/interface/SelectionTable.h"
#include "TopTreeAnalysisBase/Selection/interface/Run2Selection.h"

#include "TopTreeAnalysisBase/Content/interface/AnalysisEnvironment.h"
#include "TopTreeAnalysisBase/Content/interface/Dataset.h"
#include "TopTreeAnalysisBase/Tools/interface/JetTools.h"
#include "TopTreeAnalysisBase/Tools/interface/PlottingTools.h"
#include "TopTreeAnalysisBase/Tools/interface/MultiSamplePlot.h"
#include "TopTreeAnalysisBase/Tools/interface/TTreeLoader.h"
#include "TopTreeAnalysisBase/Tools/interface/AnalysisEnvironmentLoader.h"
#include "TopTreeAnalysisBase/Reconstruction/interface/JetCorrectorParameters.h"
#include "TopTreeAnalysisBase/Reconstruction/interface/JetCorrectionUncertainty.h"
#include "TopTreeAnalysisBase/Reconstruction/interface/MakeBinning.h"
#include "TopTreeAnalysisBase/MCInformation/interface/LumiReWeighting.h"
#include "TopTreeAnalysisBase/MCInformation/interface/JetPartonMatching.h"
#include "TopTreeAnalysisBase/Reconstruction/interface/MEzCalculator.h"
#include "TopTreeAnalysisBase/Tools/interface/LeptonTools.h"

#include "TopTreeAnalysisBase/Reconstruction/interface/TTreeObservables.h"

// This header file is taken directly from the BTV wiki. It contains
// to correctly apply an event level Btag SF. It is not yet on CVS
// as I hope to merge the functionality into BTagWeigtTools.h
//#include "TopTreeAnalysisBase/Tools/interface/BTagSFUtil.h"
#include "TopTreeAnalysisBase/Tools/interface/BTagWeightTools.h"

#include "TopTreeAnalysisBase/Tools/interface/JetCombiner.h"
#include "TopTreeAnalysisBase/Tools/interface/MVATrainer.h"
#include "TopTreeAnalysisBase/Tools/interface/MVAComputer.h"
#include "TopTreeAnalysisBase/Tools/interface/JetTools.h"

using namespace std;
using namespace TopTree;

struct HighestCVSBtag {
    bool operator()(TRootJet* j1, TRootJet* j2) const
    {
        return j1->btag_combinedInclusiveSecondaryVertexV2BJetTags() >
            j2->btag_combinedInclusiveSecondaryVertexV2BJetTags();
    }
};

float Sphericity(vector<TLorentzVector> parts);
float Centrality(vector<TLorentzVector> parts);

int main(int argc, char** argv)
{
string chan;

if(argc > 0) {
        int iarg = 1;
        if(argc > 1) {
            iarg = 1;
            string val = argv[iarg];
            if(val.find("--chan") != std::string::npos) {
                iarg++;
                chan = argv[iarg];
                cout << "now selecting channel : " << chan << endl;
            }
        } else {
            cout << "no arguments supplied" << endl;
            return 0;
        }
}


    clock_t start = clock();
    string xmlFileName = "/user/heilman/CMSSW_7_6_3/src/TopBrussels/FourTops/config/Run2DiLepton_BDTTrain.xml";

    const char* xmlfile = xmlFileName.c_str();
    cout << "used config file: " << xmlfile << endl;

    /////////////////////////////
    /// AnalysisEnvironment
    /////////////////////////////

    //    AnalysisEnvironment anaEnv;
    //    cout << " - Loading environment ..." << endl;
    //    AnalysisEnvironmentLoader anaLoad(anaEnv, xmlfile);
    //    int verbose = 2; // anaEnv.Verbose;
    /////////////////////////////
    //  Set up AnalysisEnvironment
    /////////////////////////////

    AnalysisEnvironment anaEnv;
    cout << " - Creating environment ..." << endl;
    //    AnalysisEnvironmentLoader anaLoad(anaEnv,xmlfile);
    anaEnv.PrimaryVertexCollection = "PrimaryVertex";
    anaEnv.JetCollection = "PFJets_slimmedJets";
    anaEnv.FatJetCollection = "FatJets_slimmedJetsAK8";
    anaEnv.METCollection = "PFMET_slimmedMETs";
    anaEnv.MuonCollection = "Muons_slimmedMuons";
    anaEnv.ElectronCollection = "Electrons_slimmedElectrons";
    anaEnv.GenJetCollection = "GenJets_slimmedGenJets";
    //    anaEnv.TrackMETCollection = "";
    //    anaEnv.GenEventCollection = "GenEvent";
    anaEnv.NPGenEventCollection = "NPGenEvent";
    anaEnv.MCParticlesCollection = "MCParticles";
    anaEnv.loadFatJetCollection = true;
    anaEnv.loadGenJetCollection = false;
    //    anaEnv.loadGenEventCollection = false;
    anaEnv.loadNPGenEventCollection = false;
    anaEnv.loadMCParticles = true;
    //    anaEnv.loadTrackMETCollection = false;
    anaEnv.JetType = 2;
    anaEnv.METType = 2;
    int verbose = 2; // anaEnv.Verbose;

    ////////////////////////////////
    //  Load datasets
    ////////////////////////////////

    TTreeLoader treeLoader;
    vector<Dataset*> datasets;
    cout << " - Loading datasets ..." << endl;
    treeLoader.LoadDatasets(datasets, xmlfile);
    float Luminosity = 2000.0; // pb^-1??
    vector<string> MVAvars;

    int targetNSignalEvents = 5000;

    // A few bools to steer the MassReco and Event MVAs
    string MVAmethod = "BDT";

    int nTags;
    double H, HTH, HT, HTHi, HTb, HTRat, HT2M;
    int jet_flavor;
    double JetPt, JetEta;
    double SF_tag = 1.;
    float workingpointvalue = 0.890; // working points updated to 2015 BTV-POG recommendations.

    cout << "Instantiating jet combiner..." << endl;

    JetCombiner* jetCombiner = new JetCombiner(false, 1000.0, datasets, MVAmethod, false);
    cout << "Instantiated jet combiner..." << endl;

    // vector of objects
    cout << " - Variable declaration ..." << endl;
    vector<TRootVertex*> vertex;
    vector<TRootMuon*> init_muons;
    vector<TRootElectron*> init_electrons;
    vector<TRootJet*> init_jets;
    vector<TRootJet*> init_fatjets;
    vector<TRootMET*> mets;

    bool debug = false;
    bool singlelep = false;
    bool dilep = true;
    bool Muon = true;
    bool Electron = true;
    bool Combined = false;
    int nPassed = 0;

    if(chan.find("muel") != std::string::npos)
    {
        Muon = true;
        Electron = true;
    }
    else if(chan.find("mumu") != std::string::npos)
    {
        Muon = true;
        Electron = false;
    }
    else if(chan.find("elel") != std::string::npos)
    {
        Muon = false;
        Electron = true;
    }
    else if(chan.find("comb") != std::string::npos)
    {
        Muon = false;
        Electron = false;
        Combined = true;
    }

    //    BTagWeightTools * bTool = new BTagWeightTools("SFb-pt_NOttbar_payload_EPS13.txt", "CSVM") ;

    int dobTagEffShift = 0; // 0: off (except nominal scalefactor for btag eff) 1: minus 2: plus
    cout << "dobTagEffShift: " << dobTagEffShift << endl;

    int domisTagEffShift = 0; // 0: off (except nominal scalefactor for mistag eff) 1: minus 2: plus
    cout << "domisTagEffShift: " << domisTagEffShift << endl;

    // Global variable
    TRootEvent* event = 0;

    MVATrainer* Eventtrainer_;

    if(dilep && Muon && Electron) {
        Eventtrainer_ = new MVATrainer("BDT", "MasterMVA_MuEl_26thOctober", "MVA/MasterMVA_MuEl_26thOctober.root");
    } else if(dilep && Muon && !Electron) {
        Eventtrainer_ = new MVATrainer("BDT", "MasterMVA_MuMu_26thOctober", "MVA/MasterMVA_MuMu_26thOctober.root");
    } else if(dilep && !Muon && Electron) {
        Eventtrainer_ = new MVATrainer("BDT", "MasterMVA_ElEl_26thOctober", "MVA/MasterMVA_ElEl_26thOctober.root");
    } else if(dilep && !Muon && !Electron && Combined) {
        Eventtrainer_ = new MVATrainer("BDT", "MasterMVA_DiLep_Combined_26thOctober", "MVA/MasterMVA_DiLep_Combined_26thOctober.root");
    } else if(singlelep) {
        Eventtrainer_ =
            new MVATrainer("BDT", "MasterMVA_SingleMuon_2ndOctober", "MVA/MasterMVA_SingleMuon_2ndOctober.root");
    }

    if(dilep) {
        Eventtrainer_->bookWeight("Weight");
        Eventtrainer_->bookInputVar("topness");
        Eventtrainer_->bookInputVar("LeadLepPt");
        Eventtrainer_->bookInputVar("LeadLepEta");
        Eventtrainer_->bookInputVar("HTH");
        Eventtrainer_->bookInputVar("HTRat");
        Eventtrainer_->bookInputVar("HTb");
        Eventtrainer_->bookInputVar("nLtags");
        Eventtrainer_->bookInputVar("nMtags");
        Eventtrainer_->bookInputVar("nTtags");
        Eventtrainer_->bookInputVar("nJets");
//        Eventtrainer_->bookInputVar("Jet3Pt");
//        Eventtrainer_->bookInputVar("Jet4Pt");
        Eventtrainer_->bookInputVar("HT2M");
        Eventtrainer_->bookInputVar("EventSph");
//        Eventtrainer_->bookInputVar("EventCen");
//        Eventtrainer_->bookInputVar("DiLepSph");
//        Eventtrainer_->bookInputVar("DiLepCen");
//        Eventtrainer_->bookInputVar("TopDiLepSph");
//        Eventtrainer_->bookInputVar("TopDiLepCen");
    } else if(singlelep) {

        // Eventtrainer_->bookWeight("Weight");
        Eventtrainer_->bookInputVar("multitopness");
        Eventtrainer_->bookInputVar("muonpt");
        Eventtrainer_->bookInputVar("muoneta");
        Eventtrainer_->bookInputVar("HTH");
        Eventtrainer_->bookInputVar("HTRat");
        Eventtrainer_->bookInputVar("HTb");
        Eventtrainer_->bookInputVar("nLtags");
        Eventtrainer_->bookInputVar("nMtags");
        Eventtrainer_->bookInputVar("nTtags");
        Eventtrainer_->bookInputVar("nJets");
        Eventtrainer_->bookInputVar("Jet5Pt");
        Eventtrainer_->bookInputVar("Jet6Pt");
    }

    //    TRootGenEvent* genEvt = 0;
    int event_start = 0;

    cout << "  N datsets = " << datasets.size() << endl;

    for(unsigned int d = 0; d < datasets.size(); d++) {
        cout << "Beginning dataset loop: " << datasets[d]->Name() << " with " << datasets[d]->NofEvtsToRunOver()
             << " events." << endl;
        unsigned int ending = datasets[d]->NofEvtsToRunOver();
        int start = 0, iFile = -1;
        int previousRun = -1;
        vector<int> itrigger;
        cout << "Number of events in total dataset = " << ending << endl;
        event_start = 0;
        nPassed = 0;
        string previousFilename = "";
        string dataSetName = datasets[d]->Name();
        float centralWeight = 0;

        if(dataSetName.find("MuEl") == string::npos && dilep && Muon && Electron) {
            continue;
        } else if(dataSetName.find("MuMu") == string::npos && dilep && Muon && !Electron) {
            continue;
        } else if(dataSetName.find("ElEl") == string::npos && dilep && !Muon && Electron) {
            continue;
        } else if(dataSetName.find("Combined") == string::npos && dilep && !Muon && !Electron && Combined) {
            continue;
        } else {
        }

        cout << "Dataset loop..." << endl;
        cout << " dataset name " << datasets[d]->Name() << endl;
        treeLoader.LoadDataset(datasets[d], anaEnv); // open files and load dataset

        for(unsigned int ievt = 0; ievt < ending; ievt++) {

            if(ievt % 10000 == 0 && nPassed < 5000) {
                std::cout << "Processing the " << ievt
                          << "th event, time = " << ((double)clock() - start) / CLOCKS_PER_SEC << " ("
                          << 100 * (ievt - start) / (ending) << "%)" << flush << "\r" << endl;
            }
            if(nPassed >= (0.41*targetNSignalEvents) && dataSetName.find("tttt") == string::npos)
                continue;
            else if(nPassed >= targetNSignalEvents && dataSetName.find("tttt") != string::npos)
                continue;

            // define object containers
            vector<TRootJet*> selectedLBJets;
            vector<TRootJet*> selectedMBJets;
            vector<TRootJet*> selectedTBJets;
            vector<TRootElectron *> selectedElectrons, selectedLooseElectrons, selectedMediumElectrons,
                selectedTightElectrons, selectedLooseXElectrons, selectedMediumXElectrons, selectedPosTightElectrons,
                selectedNegTightElectrons, selectedPosNTightElectrons, selectedNegNTightElectrons;
            vector<TRootPFJet *> selectedJets, selectedUncleanedJets;
            vector<TRootJet*> selectedLightJets;
            vector<TRootJet*> selectedBJets;
            vector<TRootMuon*> selectedMuons, selectedPosMuons, selectedNegMuons;
            vector<TRootElectron*> selectedExtraElectrons;
            vector<TRootMuon*> selectedExtraMuons;
            vector<TRootMCParticle*> mcParticlesMatching_;
            vector<TRootPFJet*> selectedJets2ndPass;

            mcParticlesMatching_.clear();
            //            genEvt = treeLoader.LoadGenEvent(ievt,false);
            treeLoader.LoadMCEvent(ievt, 0, mcParticlesMatching_, false);
            HT = 0;
            H = 0;
            HTH = 0;
            HTHi = 0;
            nTags = 0;
            HTb = 0;
            HT2M = 0;
            selectedLBJets.clear();
            selectedMBJets.clear();
            selectedTBJets.clear();

//            if(ievt % 1000 == 0) {
//                cout << "Loading Event" << endl;
//            }

            event = treeLoader.LoadEvent(
                ievt, vertex, init_muons, init_electrons, init_jets, init_fatjets, mets, debug); // load event

//            if(ievt % 1000 == 0) {
//                cout << "Event Loaded" << endl;
//                                cin.get();
//            }

            int currentRun = event->runId();
            //            int itrigger = -1;
            bool trigged = false;

            string currentFilename = datasets[d]->eventTree()->GetFile()->GetName();
            if(previousFilename != currentFilename) {
                previousFilename = currentFilename;
                iFile++;
                cout << "File changed!!! => " << currentFilename << endl;
            }
            if(previousRun != currentRun) {
                cout << "What run? " << currentRun << endl;
                previousRun = currentRun;
                if(Muon && Electron) {
                    itrigger.push_back(
                        treeLoader.iTrigger("HLT_Mu17_TrkIsoVVL_Ele12_CaloIdL_TrackIdL_IsoVL_v*", currentRun, iFile));
                    itrigger.push_back(
                        treeLoader.iTrigger("HLT_Mu8_TrkIsoVVL_Ele17_CaloIdL_TrackIdL_IsoVL_v*", currentRun, iFile));
                    //                        cout << "iTrigger : " << itrigger << " iFile: " << iFile << endl;
                    //                        cout << "runInfos Trigger : " <<
                    //                        runInfos->getHLTinfo(currentRun).hltPath("HLT_Mu17_TrkIsoVVL_Ele12_CaloIdL_TrackIdL_IsoVL_v1")
                    //                        << endl;
                } else if(Muon && !Electron) {
                    itrigger.push_back(
                        treeLoader.iTrigger("HLT_Mu17_TrkIsoVVL_TkMu8_TrkIsoVVL_DZ_v*", currentRun, iFile));
                    // itrigger.push_back(treeLoader.iTrigger ("HLT_IsoMu20_v*", currentRun, iFile));
                } else if(!Muon && Electron) {
                    itrigger.push_back(
                        treeLoader.iTrigger("HLT_Ele17_Ele12_CaloIdL_TrackIdL_IsoVL_DZ_v*", currentRun, iFile));
                } else if(!Muon && !Electron && Combined) {
                    itrigger.push_back(
                        treeLoader.iTrigger("HLT_Mu17_TrkIsoVVL_Ele12_CaloIdL_TrackIdL_IsoVL_v*", currentRun, iFile));
                    itrigger.push_back(
                        treeLoader.iTrigger("HLT_Mu8_TrkIsoVVL_Ele17_CaloIdL_TrackIdL_IsoVL_v*", currentRun, iFile));
                    itrigger.push_back(
                        treeLoader.iTrigger("HLT_Mu17_TrkIsoVVL_TkMu8_TrkIsoVVL_DZ_v*", currentRun, iFile));
                    itrigger.push_back(
                        treeLoader.iTrigger("HLT_Ele17_Ele12_CaloIdL_TrackIdL_IsoVL_DZ_v*", currentRun, iFile));
                }
                    // itrigger.push_back(treeLoader.iTrigger ("HLT_IsoMu20_v*", currentRun, iFile));
                for(int tr = 0; tr < itrigger.size(); tr++) {
                    if(itrigger[tr] == 9999) {
                        cerr << "NO VALID TRIGGER FOUND FOR THIS EVENT (" << dataSetName << ") IN RUN "
                             << event->runId() << endl;
                        exit(1);
                    }
                }
            }
            for(int tr = 0; tr < itrigger.size(); tr++) {
                bool temp = (treeLoader.EventTrigged(itrigger[tr]) || trigged);
                trigged = temp;
            }

            if(!trigged)
                continue; // without HLT don't keep going

            float rho = event->fixedGridRhoFastjetAll();

            // Declare selection instance
            Run2Selection selection(init_jets, init_fatjets, init_muons, init_electrons, mets, rho);

            if(Muon && Electron) {

                if(debug)
                    cout << "Getting Loose Muons" << endl;
                selectedMuons = selection.GetSelectedMuons(20, 2.4, 0.25, "Loose", "Spring15");
                selectedExtraMuons = selection.GetSelectedMuons(0, 2.4, 1, "Loose", "Spring15");
                if(debug)
                    cout << "Getting Loose Electrons" << endl;
                selectedElectrons = selection.GetSelectedElectrons(25, 2.5, "Loose", "Spring15_25ns", true); // VBTF ID
                selectedMediumElectrons =
                    selection.GetSelectedElectrons(25, 2.5, "Medium", "Spring15_25ns", true); // VBTF ID
                selectedTightElectrons =
                    selection.GetSelectedElectrons(25, 2.5, "Tight", "Spring15_25ns", true); // VBTF ID
            }
            else if(Muon && !Electron) {
                if(debug)
                    cout << "Getting Loose Muons" << endl;
                selectedMuons = selection.GetSelectedMuons(20, 2.4, 0.25, "Loose", "Spring15");
                if(debug)
                    cout << "Getting Loose Electrons" << endl;
                selectedElectrons = selection.GetSelectedElectrons(25, 2.5, "Loose", "Spring15_25ns", true); // VBTF ID
                selectedMediumElectrons =
                    selection.GetSelectedElectrons(25, 2.5, "Medium", "Spring15_25ns", true); // VBTF ID
                selectedTightElectrons =
                    selection.GetSelectedElectrons(25, 2.5, "Tight", "Spring15_25ns", true); // VBTF ID
            }
            else if(!Muon && Electron) {
                if(debug)
                    cout << "Getting Medium Muons" << endl;
                selectedMuons = selection.GetSelectedMuons(20, 2.4, 0.25, "Loose", "Spring15");
                if(debug)
                    cout << "Getting Loose Electrons" << endl;
                selectedElectrons = selection.GetSelectedElectrons(25, 2.5, "Loose", "Spring15_25ns", true); // VBTF ID
                selectedMediumElectrons =
                    selection.GetSelectedElectrons(25, 2.5, "Medium", "Spring15_25ns", true); // VBTF ID
                selectedTightElectrons =
                    selection.GetSelectedElectrons(25, 2.5, "Tight", "Spring15_25ns", true); // VBTF ID
            }
            else if(!Muon && !Electron && Combined) {
                if(debug)
                    cout << "Getting Medium Muons" << endl;
                selectedMuons = selection.GetSelectedMuons(20, 2.4, 0.25, "Loose", "Spring15");
                if(debug)
                    cout << "Getting Loose Electrons" << endl;
                selectedElectrons = selection.GetSelectedElectrons(25, 2.5, "Loose", "Spring15_25ns", true); // VBTF ID
                selectedMediumElectrons =
                    selection.GetSelectedElectrons(25, 2.5, "Medium", "Spring15_25ns", true); // VBTF ID
                selectedTightElectrons =
                    selection.GetSelectedElectrons(25, 2.5, "Tight", "Spring15_25ns", true); // VBTF ID
            }
            for(int l = 0; l < selectedElectrons.size();
                l++) // These loops populate electron collections exclusively so that electrons that pass the
            {
                // tight ID are not present in the lower collections.  Same for the Medium ID.
                bool isMed = false;
                for(int m = 0; m < selectedMediumElectrons.size(); m++) {
                    if(selectedElectrons[l]->Pt() == selectedMediumElectrons[m]->Pt() &&
                        selectedElectrons[l]->Eta() == selectedMediumElectrons[m]->Eta())
                        isMed = true;
                }
                if(!isMed) {
                    selectedLooseXElectrons.push_back(selectedElectrons[l]);
                    if(selectedElectrons[l]->charge() == 1)
                        selectedPosNTightElectrons.push_back(selectedElectrons[l]);
                    else if(selectedElectrons[l]->charge() == -1)
                        selectedNegNTightElectrons.push_back(selectedElectrons[l]);
                }
            }
            for(int m = 0; m < selectedMediumElectrons.size(); m++) {
                bool isTight = false;
                for(int t = 0; t < selectedTightElectrons.size(); t++) {
                    if(selectedTightElectrons[t]->Pt() == selectedMediumElectrons[m]->Pt() &&
                        selectedTightElectrons[t]->Eta() == selectedMediumElectrons[m]->Eta())
                        isTight = true;
                }
                if(!isTight) {
                    selectedMediumXElectrons.push_back(selectedMediumElectrons[m]);
                    if(selectedMediumElectrons[m]->charge() == 1)
                        selectedPosNTightElectrons.push_back(selectedMediumElectrons[m]);
                    else if(selectedMediumElectrons[m]->charge() == -1)
                        selectedNegNTightElectrons.push_back(selectedMediumElectrons[m]);
                }
            }
            for(int t = 0; t < selectedTightElectrons.size(); t++) {
                if(selectedTightElectrons[t]->charge() == 1)
                    selectedPosTightElectrons.push_back(selectedTightElectrons[t]);
                else if(selectedTightElectrons[t]->charge() == -1)
                    selectedNegTightElectrons.push_back(selectedTightElectrons[t]);
            }

            if(debug)
                cout << "Getting Jets" << endl;
            selectedUncleanedJets =
                selection.GetSelectedJets(30, 2.5, true, "Loose"); // Relying solely on cuts defined in setPFJetCuts()
            //            selectedLooseJets = selection.GetSelectedJets();       // Relying solely on cuts defined in
            //            setPFJetCuts()
            //            selectedFatJets = selection.GetSelectedFatJets();      // Relying solely on cuts defined in
            //            setPFJetCuts()
            for(int unj = 0; unj < selectedUncleanedJets.size(); unj++) {
                bool isClose = false;
                for(int e = 0; e < selectedElectrons.size(); e++) {
                    if(selectedElectrons[e]->DeltaR(*selectedUncleanedJets[unj]) < 0.3)
                        isClose = true;
                }
                for(int mu = 0; mu < selectedMuons.size(); mu++) {
                    if(selectedMuons[mu]->DeltaR(*selectedUncleanedJets[unj]) < 0.3)
                        isClose = true;
                }
                if(!isClose)
                    selectedJets.push_back(selectedUncleanedJets[unj]);
            }
            int nJets = selectedJets.size(); // Number of Jets in Event
            int nMu = 0, nEl = 0, nLooseIsoMu = 0, nLep = 0, nLooseEl = 0, nMedEl = 0, nTightEl = 0;

            nMu = selectedMuons.size();                // Number of Muons in Event
            nEl = selectedElectrons.size();            // Number of Loose Electrons in Event
            nLooseEl = selectedLooseXElectrons.size(); // Number of Loose Electrons in Event
            nMedEl = selectedMediumXElectrons.size();  // Number of Loose Electrons in Event
            nTightEl = selectedTightElectrons.size();  // Number of Loose Electrons in Event
            nLep = nMu + nEl;
            
            bool isTagged = false;
            vector<TLorentzVector> selectedMuonsTLV_JC, selectedElectronsTLV_JC, selectedLooseIsoMuonsTLV;
            vector<TLorentzVector> mcParticlesTLV, selectedJetsTLV, mcMuonsTLV, mcPartonsTLV;
            vector<int> mcMuonIndex, mcPartonIndex;
            JetPartonMatching muonMatching, jetMatching;

            //////////////////////////////////
            // Preselection Lepton Operations //
            //////////////////////////////////

            float diLepMass = 0, diMuMass = 0;
            bool ZVeto = false, sameCharge = false;
            float ZMass = 91, ZMassWindow = 15;
            int cj1 = 0, cj2 = 0, lidx1 = 0, lidx2 = 0;
            TLorentzVector lep1, lep2, diLep;
            for(int selmu = 0; selmu < selectedMuons.size(); selmu++) {
                selectedMuonsTLV_JC.push_back(*selectedMuons[selmu]);
            }

            for(int selel = 0; selel < selectedElectrons.size(); selel++) {
                selectedElectronsTLV_JC.push_back(*selectedElectrons[selel]);
            }

            if(nMu >= 2 && nEl == 0 && ((Muon && !Electron) || Combined)) // Di-Muon Selection
            {
                if(selectedPosMuons.size() > 0 && selectedNegMuons.size() > 0) {
                    lep1 = (TLorentzVector)*selectedPosMuons[0];
                    lep2 = (TLorentzVector)*selectedNegMuons[0];
                    sameCharge = true;
                } else {
                    lep1 = selectedMuonsTLV_JC[0];
                    lep2 = selectedMuonsTLV_JC[1];
                }
            } else if(nTightEl >= 1 && nEl >= 2 && nMu == 0 && ((Electron && !Muon) || Combined)) // Di-Electron Selection criteria
            {
                if(selectedPosTightElectrons.size() > 0 && selectedNegTightElectrons.size() > 0) {
                    lep1 = (TLorentzVector)*selectedPosTightElectrons[0];
                    lep2 = (TLorentzVector)*selectedNegTightElectrons[0];
                    sameCharge = true;
                } else if(selectedPosTightElectrons.size() > 0 && selectedNegNTightElectrons.size() > 0) {
                    lep1 = (TLorentzVector)*selectedPosTightElectrons[0];
                    lep2 = (TLorentzVector)*selectedNegNTightElectrons[0];
                    sameCharge = true;
                } else if(selectedNegTightElectrons.size() > 0 && selectedPosNTightElectrons.size() > 0) {
                    lep1 = (TLorentzVector)*selectedNegTightElectrons[0];
                    lep2 = (TLorentzVector)*selectedPosNTightElectrons[0];
                    sameCharge = true;
                } else {
                    lep1 = (TLorentzVector)*selectedTightElectrons[0]; // Always set the first lepton to the highest Pt
                                                                       // Tight Electron
                    if(nTightEl >= 2) // If there is a second Tight Electron use that one
                    {
                        lep2 = (TLorentzVector)*selectedTightElectrons[1];
                    } else if(nMedEl >= 1) // If no second Tight electron use the highest Pt Medium if present
                    {
                        lep2 = (TLorentzVector)*selectedMediumXElectrons[0];
                    } else // In the absence of other second electrons use the highest Pt Loose one
                    {
                        lep2 = (TLorentzVector)*selectedLooseXElectrons[0];
                    }
                }
            } else if(nTightEl >= 1 && nEl >= 1 && nMu >= 1 && ((Electron && Muon) || Combined)) // Muon-Electron Selection
            {
                lep1 = (TLorentzVector)*selectedMuons[0];
                lep2 = (TLorentzVector)*selectedTightElectrons[0];
                if(selectedElectrons[0]->charge() == selectedMuons[0]->charge())
                    sameCharge = true;
            }
            sort(selectedJets.begin(), selectedJets.end(), HighestCVSBtag());

            for(Int_t seljet1 = 0; seljet1 < selectedJets.size(); seljet1++) {
                selectedJetsTLV.push_back(*selectedJets[seljet1]);
                HT += selectedJets[seljet1]->Pt();
                H += selectedJets[seljet1]->P();

                if(dilep) {
                    if(seljet1 >= 2) {
                        HT2M = HT2M + selectedJets[seljet1]->Pt();
                    }
                    if(seljet1 > 2)
                        HTHi += selectedJets[seljet1]->Pt();
                } else if(singlelep) {

                    if(seljet1 > 4)
                        HTHi += selectedJets[seljet1]->Pt();
                }
            }

            HTRat = HTHi / HT;
            HTH = HT / H;

            for(Int_t seljet = 0; seljet < selectedJets.size(); seljet++) {
                if(selectedJets[seljet]->btag_combinedInclusiveSecondaryVertexV2BJetTags() > 0.800) {
                    selectedMBJets.push_back(selectedJets[seljet]);
                    HTb += selectedJets[seljet]->Pt();
                }

                if(selectedJets[seljet]->btag_combinedInclusiveSecondaryVertexV2BJetTags() > 0.460)
                    selectedLBJets.push_back(selectedJets[seljet]);
                if(selectedJets[seljet]->btag_combinedInclusiveSecondaryVertexV2BJetTags() > 0.935)
                    selectedTBJets.push_back(selectedJets[seljet]);
            }

            int nLtags = selectedLBJets.size(); // Number of CSVM tags in Event
            int nMtags = selectedMBJets.size(); // Number of CSVM tags in Event
            int nTtags = selectedTBJets.size(); // Number of CSVM tags in Event
            int nLooseMu = selectedExtraMuons.size();

            if(dilep && (nMu >= 1 && nTightEl >= 1) && ((Muon && Electron) || Combined)) {
                if(!(selectedMuons[0]->Pt() <= 1000 && selectedElectrons[0]->Pt() <= 1000))
                    continue; // Muon-Electron Channel Selection
                if(!(nJets >= 4))
                    continue; // Muon-Electron Channel Selection
                if(!(nMtags >= 2))
                    continue; // Muon-Electron Channel Selection
                if(!(HT >= 500))
                    continue; // Muon-Electron Channel Selection
                if(!(mets[0]->Et() <= 1000))
                    continue; // Muon-Electron Channel Selection
                if(Combined && nPassed < 100) cout << "Combined MuEl Selected" << endl;
            } else if(dilep && (nMu >= 2 && nEl == 0) && ((Muon && !Electron) || Combined)) {
                if(!(selectedMuons[0]->Pt() <= 1000 && selectedMuons[1]->Pt() <= 1000))
                    continue; // Muon-Electron Channel Selection
                TLorentzVector diMu = lep1 + lep2;
                float diMuMass = diMu.M();
                if(diMuMass < 20 || (diMuMass > 76 && diMuMass < 106))
                    ZVeto = true;
                if(ZVeto)
                    continue;
                if(!(nJets >= 4))
                    continue; // Muon-Electron Channel Selection
                if(!(nMtags >= 2))
                    continue; // Muon-Electron Channel Selection
                if(!(HT >= 500))
                    continue; // Muon-Electron Channel Selection
                if(!(mets[0]->Et() <= 1000))
                    continue; // Muon-Electron Channel Selection
                if(Combined && nPassed < 100) cout << "Combined MuMu Selected" << endl;
            } else if(dilep && (nMu == 0 && nTightEl >= 1 && nEl >= 2) && ((!Muon && Electron) || Combined)) {
                if(!(selectedTightElectrons[0]->Pt() <= 1000 && selectedElectrons[1]->Pt() <= 1000))
                    continue; // Muon-Electron Channel Selection
                TLorentzVector diEl = lep1 + lep2;
                float diElMass = diEl.M();
                if(diElMass < 20 || (diElMass > 76 && diElMass < 106))
                    ZVeto = true;
                if(ZVeto)
                    continue;
                if(!(nJets >= 4))
                    continue; // Muon-Electron Channel Selection
                if(!(nMtags >= 2))
                    continue; // Muon-Electron Channel Selection
                if(!(HT >= 500))
                    continue; // Muon-Electron Channel Selection
                if(!(mets[0]->Et() <= 1000))
                    continue; // Muon-Electron Channel Selection
                if(Combined && nPassed < 100) cout << "Combined ElEl Selected" << endl;
            } else if(singlelep) {
                if(!(nMu == 1 && nEl == 0 && nLooseMu == 1))
                    continue; // Muon + jets Channel Selection
                if(!(nJets >= 6))
                    continue; // Muon + jets Channel Selection
                if(!(nMtags >= 2))
                    continue; // Muon + jets Channel Selection
            }
            else continue;

            if(debug)
                cout << "event passed - " << datasets[d]->Name() << " njets  " << nJets << " ntags " << nMtags << endl;
            nPassed++;
            if(nPassed % 100 == 0) {
                std::cout << nPassed << " events have passed baseline selection" << endl;
            }

            if(dilep) {
                jetCombiner->ProcessEvent_SingleHadTop(
                    datasets[d], mcParticlesMatching_, selectedJets, &lep1, 1.);
            } else {
                jetCombiner->ProcessEvent_SingleHadTop(
                    datasets[d], mcParticlesMatching_, selectedJets, &selectedMuonsTLV_JC[0], 1.);
            }

            pair<float, vector<unsigned int> > MVAvals1;
            MVAvals1 = jetCombiner->getMVAValue(MVAmethod, 1);

            double topness = MVAvals1.first;

            selectedJets2ndPass.clear();

            pair<float, vector<unsigned int> > MVAvals2ndPass;

            // make vector of jets excluding thise selected by 1st pass of mass reco
            for(Int_t seljet3 = 0; seljet3 < selectedJets.size(); seljet3++) {
                if(seljet3 == MVAvals1.second[0] || seljet3 == MVAvals1.second[1] || seljet3 == MVAvals1.second[2]) {
                    //   MVASelJets1.push_back(selectedJets[seljet3]);
                    continue;
                }
                selectedJets2ndPass.push_back(selectedJets[seljet3]);
            }

            double multitopness = 0;
            double leadLepPt = 0, leadLepEta = 0, muonpt = 0, muoneta = 0;

            if(dilep && nTightEl >= 1 && nEl >= 1 && nMu >= 1 && ((Electron && Muon) || Combined)) {
                leadLepPt = (selectedMuons[0]->Pt() > selectedElectrons[0]->Pt() ? selectedMuons[0]->Pt() :
                                                                                   selectedElectrons[0]->Pt());
                leadLepEta = (selectedMuons[0]->Pt() > selectedElectrons[0]->Pt() ? selectedMuons[0]->Eta() :
                                                                                    selectedElectrons[0]->Eta());
            } else if(dilep && nMu >= 2 && nEl == 0 && ((Muon && !Electron) || Combined)) {
                leadLepPt = selectedMuons[0]->Pt();
                leadLepEta = selectedMuons[0]->Eta();
            } else if(dilep && nTightEl >= 1 && nEl >= 2 && nMu == 0 && ((Electron && !Muon) || Combined)) {
                leadLepPt = selectedTightElectrons[0]->Pt();
                leadLepEta = selectedTightElectrons[0]->Eta();
            }

            if(nJets >= 6  && !dilep) {
                if(!Muon && Electron) {
                    jetCombiner->ProcessEvent_SingleHadTop(
                        datasets[d], mcParticlesMatching_, selectedJets, &selectedElectronsTLV_JC[0], 1.);
                    muonpt = selectedElectronsTLV_JC[0].Pt();
                    muoneta = selectedElectronsTLV_JC[0].Eta();
                } else {
                    jetCombiner->ProcessEvent_SingleHadTop(
                        datasets[d], mcParticlesMatching_, selectedJets, &selectedMuonsTLV_JC[0], 1.);
                    muonpt = selectedMuons[0]->Pt();
                    muoneta = selectedMuons[0]->Eta();
                }
                MVAvals2ndPass = jetCombiner->getMVAValue(MVAmethod, 1);

                multitopness = MVAvals2ndPass.first;
            }

            //  cout <<" # leftover jets " <<  selectedJets2ndPass.size()     << " multitopness  =  "<<  multitopness
            //  <<endl;
            if(dataSetName.find("TTDileptMG") != std::string::npos ||
                dataSetName.find("TTJetsMG") != std::string::npos) {
                centralWeight = (event->getWeight(1)) / (abs(event->originalXWGTUP()));
            } else if(dataSetName.find("tttt") != std::string::npos || dataSetName.find("TTTT") != std::string::npos) {
                centralWeight = (event->getWeight(1001)) / (abs(event->originalXWGTUP()));
            }
            float scaleFactor = 1.0;
            scaleFactor *= centralWeight;

            if(dilep) {
                vector<TLorentzVector> selectedParticlesTLV, diLepSystemTLV, topDiLepSystemTLV;
                // collection Total Event TLVs
                selectedParticlesTLV.insert(
                    selectedParticlesTLV.end(), selectedElectronsTLV_JC.begin(), selectedElectronsTLV_JC.end());
                selectedParticlesTLV.insert(
                    selectedParticlesTLV.end(), selectedMuonsTLV_JC.begin(), selectedMuonsTLV_JC.end());
                selectedParticlesTLV.insert(selectedParticlesTLV.end(), selectedJetsTLV.begin(), selectedJetsTLV.end());
                selectedParticlesTLV.push_back(*mets[0]);
                // collecting diLep TLVs
                diLepSystemTLV.push_back(lep1);
                diLepSystemTLV.push_back(lep2);
                diLepSystemTLV.push_back(*mets[0]);
                // collecting topDiLep TLVs
                topDiLepSystemTLV.insert(topDiLepSystemTLV.end(), diLepSystemTLV.begin(), diLepSystemTLV.end());
                topDiLepSystemTLV.push_back(*selectedJets[MVAvals1.second[0]]);
                topDiLepSystemTLV.push_back(*selectedJets[MVAvals1.second[1]]);
                topDiLepSystemTLV.push_back(*selectedJets[MVAvals1.second[2]]);

                float tSph = Sphericity(selectedParticlesTLV), tCen = Centrality(selectedParticlesTLV);
                float dSph = Sphericity(diLepSystemTLV), dCen = Centrality(diLepSystemTLV);
                float tdSph = Sphericity(topDiLepSystemTLV), tdCen = Centrality(topDiLepSystemTLV);

                if(dataSetName.find("tttt") != string::npos || dataSetName.find("TTTT") != string::npos) {
                    Eventtrainer_->FillWeight("S", "Weight", scaleFactor);
                    Eventtrainer_->Fill("S", "topness", topness);
                    Eventtrainer_->Fill("S", "LeadLepPt", leadLepPt);
                    Eventtrainer_->Fill("S", "LeadLepEta", leadLepEta);
                    Eventtrainer_->Fill("S", "HTb", HTb);
                    Eventtrainer_->Fill("S", "HTH", HTH);
                    Eventtrainer_->Fill("S", "HTRat", HTRat);
                    Eventtrainer_->Fill("S", "nLtags", nLtags);
                    Eventtrainer_->Fill("S", "nMtags", nMtags);
                    Eventtrainer_->Fill("S", "nTtags", nTtags);
                    Eventtrainer_->Fill("S", "nJets", selectedJets.size());
//                    Eventtrainer_->Fill("S", "Jet3Pt", selectedJets[2]->Pt());
//                    Eventtrainer_->Fill("S", "Jet4Pt", selectedJets[3]->Pt());
                    Eventtrainer_->Fill("S", "HT2M", HT2M);
                    Eventtrainer_->Fill("S", "EventSph", tSph);
//                    Eventtrainer_->Fill("S", "EventCen", tCen);
//                    Eventtrainer_->Fill("S", "DiLepSph", dSph);
//                    Eventtrainer_->Fill("S", "DiLepCen", dCen);
//                    Eventtrainer_->Fill("S", "TopDiLepSph", tdSph);
//                    Eventtrainer_->Fill("S", "TopDiLepCen", tdCen);
                }

                else {
                    Eventtrainer_->FillWeight("B", "Weight", scaleFactor);
                    Eventtrainer_->Fill("B", "topness", topness);
                    Eventtrainer_->Fill("B", "LeadLepPt", leadLepPt);
                    Eventtrainer_->Fill("B", "LeadLepEta", leadLepEta);
                    Eventtrainer_->Fill("B", "HTb", HTb);
                    Eventtrainer_->Fill("B", "HTRat", HTRat);
                    Eventtrainer_->Fill("B", "HTH", HTH);
                    Eventtrainer_->Fill("B", "nLtags", nLtags);
                    Eventtrainer_->Fill("B", "nMtags", nMtags);
                    Eventtrainer_->Fill("B", "nTtags", nTtags);
                    Eventtrainer_->Fill("B", "nJets", selectedJets.size());
//                    Eventtrainer_->Fill("B", "Jet3Pt", selectedJets[2]->Pt());
//                    Eventtrainer_->Fill("B", "Jet4Pt", selectedJets[3]->Pt());
                    Eventtrainer_->Fill("B", "HT2M", HT2M);
                    Eventtrainer_->Fill("B", "EventSph", tSph);
//                    Eventtrainer_->Fill("B", "EventCen", tCen);
//                    Eventtrainer_->Fill("B", "DiLepSph", dSph);
//                    Eventtrainer_->Fill("B", "DiLepCen", dCen);
//                    Eventtrainer_->Fill("B", "TopDiLepSph", tdSph);
//                    Eventtrainer_->Fill("B", "TopDiLepCen", tdCen);
                }

            } else if(singlelep) {

                if(datasets[d]->Name() == "NP_overlay_TTTT") {
                    //        Eventtrainer_->FillWeight("S","Weight",scaleFactor);
                    Eventtrainer_->Fill("S", "multitopness", multitopness);
                    Eventtrainer_->Fill("S", "LeadLepPt", muonpt);
                    Eventtrainer_->Fill("S", "LeadLepEta", muoneta);
                    Eventtrainer_->Fill("S", "HTb", HTb);
                    Eventtrainer_->Fill("S", "HTH", HTH);
                    Eventtrainer_->Fill("S", "HTRat", HTRat);
                    Eventtrainer_->Fill("S", "nLtags", nLtags);
                    Eventtrainer_->Fill("S", "nMtags", nMtags);
                    Eventtrainer_->Fill("S", "nTtags", nTtags);
                    Eventtrainer_->Fill("S", "nJets", selectedJets.size());
                    Eventtrainer_->Fill("S", "Jet5Pt", selectedJets[4]->Pt());
                    Eventtrainer_->Fill("S", "Jet6Pt", selectedJets[5]->Pt());
                }

                if(datasets[d]->Name() == "TTJets") {

                    cout << " fill ttjets tree" << endl;

                    //	   Eventtrainer_->FillWeight("B","Weight", scaleFactor);
                    Eventtrainer_->Fill("B", "multitopness", multitopness);
                    Eventtrainer_->Fill("B", "LeadLepPt", muonpt);
                    Eventtrainer_->Fill("B", "LeadLepEta", muoneta);
                    Eventtrainer_->Fill("B", "HTb", HTb);
                    Eventtrainer_->Fill("B", "HTRat", HTRat);
                    Eventtrainer_->Fill("B", "HTH", HTH);
                    Eventtrainer_->Fill("B", "nLtags", nLtags);
                    Eventtrainer_->Fill("B", "nMtags", nMtags);
                    Eventtrainer_->Fill("B", "nTtags", nTtags);
                    Eventtrainer_->Fill("B", "nJets", selectedJets.size());
                    Eventtrainer_->Fill("B", "Jet5Pt", selectedJets[4]->Pt());
                    Eventtrainer_->Fill("B", "Jet6Pt", selectedJets[5]->Pt());
                }
            }
        }
    }
    if(dilep && Muon && Electron) {
        Eventtrainer_->TrainMVA("Random", "", 0, 0, "", 0, 0, "_MuElOctober26th2015", true);
    } else if(dilep && Muon && !Electron) {
        Eventtrainer_->TrainMVA("Random", "", 0, 0, "", 0, 0, "_MuMuOctober26th2015", true);
    } else if(dilep && !Muon && Electron) {
        Eventtrainer_->TrainMVA("Random", "", 0, 0, "", 0, 0, "_ElElOctober26th2015", true);
    } else if(dilep && !Muon && !Electron && Combined) {
        Eventtrainer_->TrainMVA("Random", "", 0, 0, "", 0, 0, "_DilepCombinedOctober26th2015", true);
    }
    cout << "MVA Trained!" << endl;
    delete Eventtrainer_;
}

float Sphericity(vector<TLorentzVector> parts)
{
    if(parts.size() > 0) {
        double spTensor[3 * 3] = { 0., 0., 0., 0., 0., 0., 0., 0., 0. };
        int counter = 0;
        float tensorNorm = 0, y1 = 0, y2 = 0, y3 = 0;

        for(int tenx = 0; tenx < 3; tenx++) {
            for(int teny = 0; teny < 3; teny++) {
                for(int selpart = 0; selpart < parts.size(); selpart++) {

                    spTensor[counter] += ((parts[selpart][tenx]) * (parts[selpart][teny]));
                    //                    if((tenx == 0 && teny == 2) || (tenx == 2 && teny == 1))
                    //                    {
                    //                    cout << "nan debug term " << counter+1 << ": " <<
                    //                    (parts[selpart][tenx])*(parts[selpart][teny]) << endl;
                    //                    cout << "Tensor Building Term " << counter+1 << ": " << spTensor[counter] <<
                    //                    endl;
                    //                    }
                    if(tenx == 0 && teny == 0) {
                        tensorNorm += parts[selpart].Vect().Mag2();
                    }
                }
                if((tenx == 0 && teny == 2) || (tenx == 2 && teny == 1)) {
                    //                    cout << "Tensor term pre-norm " << counter+1 << ": " << spTensor[counter] <<
                    //                    endl;
                }
                spTensor[counter] /= tensorNorm;
                //                cout << "Tensor Term " << counter+1 << ": " << spTensor[counter] << endl;
                counter++;
            }
        }
        TMatrixDSym m(3, spTensor);
        // m.Print();
        TMatrixDSymEigen me(m);
        TVectorD eigenval = me.GetEigenValues();
        vector<float> eigenVals;
        eigenVals.push_back(eigenval[0]);
        eigenVals.push_back(eigenval[1]);
        eigenVals.push_back(eigenval[2]);
        sort(eigenVals.begin(), eigenVals.end());
        // cout << "EigenVals: "<< eigenVals[0] << ", " << eigenVals[1] << ", " << eigenVals[2] << ", " << endl;
        float sp = 3.0 * (eigenVals[0] + eigenVals[1]) / 2.0;
        // cout << "Sphericity: " << sp << endl;
        return sp;
    } else {
        return 0;
    }
}
float Centrality(vector<TLorentzVector> parts)
{
    float E = 0, ET = 0;
    for(int selpart = 0; selpart < parts.size(); selpart++) {
        E += parts[selpart].E();
        ET += parts[selpart].Et();
    }
    return ET / E;
}
