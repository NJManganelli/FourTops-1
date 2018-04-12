/////////////////////////////////////////////////////////////////////////////////
////  Stand-alone code to train and evaluate the event-level BDT on Craneens  ///
/////////////////////////////////////////////////////////////////////////////////
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
#include "TBits.h"
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
//#include "TopTreeAnalysisBase/../FourTops/SingleLepAnalysis/interface/Trigger.h"

using namespace std;
using namespace TopTree;
bool combine_eval = true;

int main(int argc, char** argv)
{
    string chan;
    bool train = false, eval = false;

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
            while(iarg < argc) {
                string val = argv[iarg];
                iarg++;
                if(val.find("--train") != std::string::npos) {
                    train = true;
                    cout << "Training an MVA" << endl;
                }
                if(val.find("--eval") != std::string::npos) {
                    eval = true;
                    cout << "Evaluating an MVA" << endl;
                }
            }
        } else {
            cerr << "no arguments supplied" << endl;
            return 0;
        }
    }
    if(train && eval) {
        cerr << "Invalid Arguments: both training and evaluation requested." << endl;
        return 0;
    }
    if(!train && !eval) {
        cerr << "Invalid Arguments: neither training nor evaluation requested." << endl;
        return 0;
    }
    clock_t start = clock();

    //////////////////////////////////////////////
    // Setup Date string and nTuple for output  //
    //////////////////////////////////////////////

    time_t t = time(0); // get time now
    struct tm* now = localtime(&t);

    int year = now->tm_year + 1900;
    int month = now->tm_mon + 1;
    int day = now->tm_mday;
    int hour = now->tm_hour;
    int min = now->tm_min;
    int sec = now->tm_sec;

    string year_str;
    string month_str;
    string day_str;
    string hour_str;
    string min_str;
    string sec_str;

    ostringstream convert; // stream used for the conversion
    convert << year;       // insert the textual representation of 'Number' in the characters in the stream
    year_str = convert.str();
    convert.str("");
    convert.clear();
    convert << month; // insert the textual representation of 'Number' in the characters in the stream
    month_str = convert.str();
    convert.str("");
    convert.clear();
    convert << day; // insert the textual representation of 'Number' in the characters in the stream
    day_str = convert.str();
    convert.str("");
    convert.clear();
    convert << hour; // insert the textual representation of 'Number' in the characters in the stream
    hour_str = convert.str();
    convert.str("");
    convert.clear();
    convert << min; // insert the textual representation of 'Number' in the characters in the stream
    min_str = convert.str();
    convert.str("");
    convert.clear();
    convert << day; // insert the textual representation of 'Number' in the characters in the stream
    sec_str = convert.str();
    convert.str("");
    convert.clear();

    string date_str = day_str + "_" + month_str + "_" + year_str;

    cout << "DATE STRING   " << date_str << endl;

    bool debug = true;
    bool Muon = false;
    bool Electron = false;
    bool Combined = false;
    int nPassed = 0;

    if(chan.find("muel") != std::string::npos) {
        Muon = true;
        Electron = true;
    } else if(chan.find("mumu") != std::string::npos) {
        Muon = true;
        Electron = false;
    } else if(chan.find("elel") != std::string::npos) {
        Muon = false;
        Electron = true;
    } else if(chan.find("comb") != std::string::npos) {
        Combined = true;
    } else {
        cerr << "Incorrect or no channel selected" << endl;
        return 0;
    }

    int targetNSignalEvents = 34000;

    // Global variable
    TRootEvent* event = 0;
    string nTuplename;

    if(Muon && Electron && !Combined) {
        nTuplename = "Craneen__MuEl";
    } else if(Muon && !Electron && !Combined) {
        nTuplename = "Craneen__MuMu";
    } else if(!Muon && Electron && !Combined) {
        nTuplename = "Craneen__ElEl";
    } else if(!Muon && !Electron && Combined) {
        nTuplename = "Craneen__Combined";
    }
    cout << "nTuplename: " << nTuplename << endl;
    if(train) {
        MVATrainer* Eventtrainer_;

        if(Muon && Electron) {
            Eventtrainer_ = new MVATrainer(
                "BDT", "MasterMVA_MuEl_13thFeb2018_13TeVHadTop", "MVA/MasterMVA_MuEl_13thFeb2018_13TeVHadTop.root");
        } else if(Muon && !Electron) {
            Eventtrainer_ = new MVATrainer(
                "BDT", "MasterMVA_MuMu_13thFeb2018_13TeVHadTop", "MVA/MasterMVA_MuMu_13thFeb2018_13TeVHadTop.root");
        } else if(!Muon && Electron) {
            Eventtrainer_ = new MVATrainer(
                "BDT", "MasterMVA_ElEl_13thFeb2018_13TeVHadTop", "MVA/MasterMVA_ElEl_13thFeb2018_13TeVHadTop.root");
        } else if(!Muon && !Electron && Combined) {
            Eventtrainer_ = new MVATrainer(
                "BDT", "MasterMVA_DiLep_Combined_13thFeb2018_13TeVHadTop", "MVA/MasterMVA_DiLep_Combined_13thFeb2018_13TeVHadTop.root");
        //            Eventtrainer_->addMethod("BDT375");
        //            Eventtrainer_->addMethod("BDT350");
        //            Eventtrainer_->addMethod("BDT4");
        //            Eventtrainer_->addMethod("BDT4375");
        //            Eventtrainer_->addMethod("BDT4350");
        }

        Eventtrainer_->bookWeight("Weight");
        Eventtrainer_->bookInputVar("nJets");
        Eventtrainer_->bookInputVar("topness");
        Eventtrainer_->bookInputVar("HTb");
        Eventtrainer_->bookInputVar("HT2M");
        Eventtrainer_->bookInputVar("HTH");
        Eventtrainer_->bookInputVar("EventSph");
        Eventtrainer_->bookInputVar("HTRat");
        Eventtrainer_->bookInputVar("leadLepPt");
        Eventtrainer_->bookInputVar("leadLepEta");
        Eventtrainer_->bookInputVar("dRLep");
        //Eventtrainer_->bookInputVar("fnjetW");
        //Eventtrainer_->bookInputVar("LepFlavor");
        //Eventtrainer_->bookInputVar("nLep");
        Eventtrainer_->bookInputVar("dRbb");
        Eventtrainer_->bookInputVar("nLtags");
        Eventtrainer_->bookInputVar("nMtags");
        //Eventtrainer_->bookInputVar("nTtags");
        Eventtrainer_->bookInputVar("Jet3Pt");
        Eventtrainer_->bookInputVar("Jet4Pt");
        //Eventtrainer_->bookInputVar("EventCen");
        //Eventtrainer_->bookInputVar("DiLepSph");
        //Eventtrainer_->bookInputVar("DiLepCen");
        //Eventtrainer_->bookInputVar("TopDiLepSph");
        //Eventtrainer_->bookInputVar("TopDiLepCen");

        bool isSignal;

        int event_start = 0;

        string filepath_tttt, filepath_ttbar;

        filepath_tttt = "/user/lowang/CMSSW_8_0_26_patch1/src/TopBrussels/FourTops/Craneens_Comb/2018_0213/NP_overlay_ttttNLO_Run2_TopTree_Study.root";
        filepath_ttbar = "/user/lowang/CMSSW_8_0_26_patch1/src/TopBrussels/FourTops/TTJetsPowheg_powheg_Run2_TopTree_Study.root";

        TFile* ttbar = new TFile(filepath_ttbar.c_str());
        TFile* tttt = new TFile(filepath_tttt.c_str());

        TNtuple* ttbar_tup = (TNtuple*)ttbar->Get(nTuplename.c_str());
        TNtuple* tttt_tup = (TNtuple*)tttt->Get(nTuplename.c_str());
        float topness_tt, topness_tttt, leadLepPt_tt, leadLepPt_tttt, leadLepEta_tt, leadLepEta_tttt, HTb_tt, HTb_tttt,
            HTRat_tt, HTRat_tttt, HTH_tt, HTH_tttt;
        float nLtags_tt, nLtags_tttt, nMtags_tt, nMtags_tttt, nTtags_tt, nTtags_tttt, nJets_tt, nJets_tttt, HT2M_tt,
            HT2M_tttt, EventSph_tt, EventSph_tttt;
        float Jet3Pt_tt, Jet3Pt_tttt, Jet4Pt_tt, Jet4Pt_tttt, EventCen_tt, EventCen_tttt, DiLepSph_tt, DiLepSph_tttt,
            DiLepCen_tt, DiLepCen_tttt, TopDiLepSph_tt, TopDiLepSph_tttt, TopDiLepCen_tt, TopDiLepCen_tttt;
        float dRLep_tt, dRLep_tttt, fnjetW_tt, fnjetW_tttt, LepFlavor_tt, LepFlavor_tttt, dRbb_tt, dRbb_tttt, nLep_tt,
            nLep_tttt;
        float weight_tt, weight_tttt, SFalphaTune_tt=1.0, SFalphaTune_tttt=1.0;

        ttbar_tup->SetBranchAddress("GenWeight", &weight_tt);
        ttbar_tup->SetBranchAddress("topness", &topness_tt);
        ttbar_tup->SetBranchAddress("LeadingLepPt", &leadLepPt_tt);
        ttbar_tup->SetBranchAddress("LeadingLepEta", &leadLepEta_tt);
        ttbar_tup->SetBranchAddress("dRLep", &dRLep_tt);
        //ttbar_tup->SetBranchAddress("fnjetW", &fnjetW_tt);
        ttbar_tup->SetBranchAddress("LepFlavor", &LepFlavor_tt);
        ttbar_tup->SetBranchAddress("nLep", &nLep_tt);
        ttbar_tup->SetBranchAddress("dRbb", &dRbb_tt);
        ttbar_tup->SetBranchAddress("HTb", &HTb_tt);
        ttbar_tup->SetBranchAddress("HTH", &HTH_tt);
        ttbar_tup->SetBranchAddress("HTRat", &HTRat_tt);
        ttbar_tup->SetBranchAddress("nLtags", &nLtags_tt);
        ttbar_tup->SetBranchAddress("nMtags", &nMtags_tt);
        ttbar_tup->SetBranchAddress("nTtags", &nTtags_tt);
        ttbar_tup->SetBranchAddress("nJets", &nJets_tt);
        ttbar_tup->SetBranchAddress("HT2M", &HT2M_tt);
        ttbar_tup->SetBranchAddress("EventSph", &EventSph_tt);
        ttbar_tup->SetBranchAddress("3rdJetPt", &Jet3Pt_tt);
        ttbar_tup->SetBranchAddress("4thJetPt", &Jet4Pt_tt);
        ttbar_tup->SetBranchAddress("EventCen", &EventCen_tt);
        ttbar_tup->SetBranchAddress("DiLepSph", &DiLepSph_tt);
        ttbar_tup->SetBranchAddress("DiLepCen", &DiLepCen_tt);
        ttbar_tup->SetBranchAddress("TopDiLepSph", &TopDiLepSph_tt);
        ttbar_tup->SetBranchAddress("TopDiLepCen", &TopDiLepCen_tt);
        //ttbar_tup->SetBranchAddress("SFalphaTune", &SFalphaTune_tt);

        tttt_tup->SetBranchAddress("GenWeight", &weight_tttt);
        tttt_tup->SetBranchAddress("topness", &topness_tttt);
        tttt_tup->SetBranchAddress("LeadingLepPt", &leadLepPt_tttt);
        tttt_tup->SetBranchAddress("LeadingLepEta", &leadLepEta_tttt);
        tttt_tup->SetBranchAddress("dRLep", &dRLep_tttt);
        //tttt_tup->SetBranchAddress("fnjetW", &fnjetW_tttt);
        tttt_tup->SetBranchAddress("LepFlavor", &LepFlavor_tttt);
        tttt_tup->SetBranchAddress("nLep", &nLep_tttt);
        tttt_tup->SetBranchAddress("dRbb", &dRbb_tttt);
        tttt_tup->SetBranchAddress("HTb", &HTb_tttt);
        tttt_tup->SetBranchAddress("HTH", &HTH_tttt);
        tttt_tup->SetBranchAddress("HTRat", &HTRat_tttt);
        tttt_tup->SetBranchAddress("nLtags", &nLtags_tttt);
        tttt_tup->SetBranchAddress("nMtags", &nMtags_tttt);
        tttt_tup->SetBranchAddress("nTtags", &nTtags_tttt);
        tttt_tup->SetBranchAddress("nJets", &nJets_tttt);
        tttt_tup->SetBranchAddress("HT2M", &HT2M_tttt);
        tttt_tup->SetBranchAddress("EventSph", &EventSph_tttt);
        tttt_tup->SetBranchAddress("3rdJetPt", &Jet3Pt_tttt);
        tttt_tup->SetBranchAddress("4thJetPt", &Jet4Pt_tttt);
        tttt_tup->SetBranchAddress("EventCen", &EventCen_tttt);
        tttt_tup->SetBranchAddress("DiLepSph", &DiLepSph_tttt);
        tttt_tup->SetBranchAddress("DiLepCen", &DiLepCen_tttt);
        tttt_tup->SetBranchAddress("TopDiLepSph", &TopDiLepSph_tttt);
        tttt_tup->SetBranchAddress("TopDiLepCen", &TopDiLepCen_tttt);
        //tttt_tup->SetBranchAddress("SFalphaTune", &SFalphaTune_tttt);


        TBits* bits_tttt = new TBits(tttt_tup->GetEntries()); // see http://root.cern.ch/root/html534/TBits.html
        TBits* bits_tt = new TBits(ttbar_tup->GetEntries());  // see http://root.cern.ch/root/html534/TBits.html
        // now assume you want to read N=1000 entries out of nentries
        Int_t N = 1000;
        Int_t i = 0;
        TRandom3 rand(0);
        while(i < tttt_tup->GetEntries()) {
            Int_t j = rand.Uniform(0, tttt_tup->GetEntries());
            if(bits_tttt->TestBitNumber(j))
                continue; // we have already seen this entry
            bits_tttt->SetBitNumber(j);
            i++;
	    if( i%1000 == 0 ) cout << i << "th signal Bit " << j << " set." << " alphaS: " << SFalphaTune_tttt << endl;
        }
        i = 0;
        while(i < ttbar_tup->GetEntries()) {
            Int_t j = rand.Uniform(0, ttbar_tup->GetEntries());
            if(bits_tt->TestBitNumber(j))
                continue; // we have already seen this entry
            bits_tt->SetBitNumber(j);
            i++;
            if( i%1000 == 0 ) cout << i << "th background Bit " << j << " set." << " alphaS: " << SFalphaTune_tt << endl;
        }
        // now loop on the N selected entries
        Int_t sbit = 0;
        Int_t bbit = 0;

        for(int j = 0; j < tttt_tup->GetEntries(); j++) {
            float scaleFactor = 1.0;
            Int_t k = bits_tttt->FirstSetBit(sbit);

            tttt_tup->GetEntry(k);

            if(weight_tttt < 0)
                scaleFactor = -1.0;
            else
                scaleFactor = 1.0;

            if(nJets_tttt >= 4) {
                Eventtrainer_->FillWeight("S", "Weight", SFalphaTune_tttt);
                Eventtrainer_->Fill("S", "topness", topness_tttt);
                Eventtrainer_->Fill("S", "leadLepPt", leadLepPt_tttt);
                Eventtrainer_->Fill("S", "leadLepEta", leadLepEta_tttt);
                Eventtrainer_->Fill("S", "dRLep", dRLep_tttt);
                //Eventtrainer_->Fill("S", "fnjetW", fnjetW_tttt);
                //Eventtrainer_->Fill("S", "LepFlavor", LepFlavor_tttt);
                //Eventtrainer_->Fill("S", "nLep", nLep_tttt);
                Eventtrainer_->Fill("S", "dRbb", dRbb_tttt);
                Eventtrainer_->Fill("S", "HTb", HTb_tttt);
                Eventtrainer_->Fill("S", "HTH", HTH_tttt);
                Eventtrainer_->Fill("S", "HTRat", HTRat_tttt);
                Eventtrainer_->Fill("S", "nLtags", nLtags_tttt);
                Eventtrainer_->Fill("S", "nMtags", nMtags_tttt);
                //Eventtrainer_->Fill("S", "nTtags", nTtags_tttt);
                Eventtrainer_->Fill("S", "nJets", nJets_tttt);
                Eventtrainer_->Fill("S", "Jet3Pt", Jet3Pt_tttt);
                Eventtrainer_->Fill("S", "Jet4Pt", Jet4Pt_tttt);
                Eventtrainer_->Fill("S", "HT2M", HT2M_tttt);
                Eventtrainer_->Fill("S", "EventSph", EventSph_tttt);
                //Eventtrainer_->Fill("S", "EventCen", EventCen_tttt);
                //Eventtrainer_->Fill("S", "DiLepSph", DiLepSph_tttt);
                //Eventtrainer_->Fill("S", "DiLepCen", DiLepCen_tttt);
                //Eventtrainer_->Fill("S", "TopDiLepSph", TopDiLepSph_tttt);
                //Eventtrainer_->Fill("S", "TopDiLepCen", TopDiLepCen_tttt);
            }
            sbit = k + 1;
        }

        for(int j = 0; j < ttbar_tup->GetEntries(); j++) {
            float scaleFactor = 1.0;
            Int_t l = bits_tt->FirstSetBit(bbit);

            ttbar_tup->GetEntry(l);

            if(nJets_tt >= 4) {
                Eventtrainer_->FillWeight("B", "Weight", SFalphaTune_tt);
                Eventtrainer_->Fill("B", "topness", topness_tt);
                Eventtrainer_->Fill("B", "leadLepPt", leadLepPt_tt);
                Eventtrainer_->Fill("B", "leadLepEta", leadLepEta_tt);
                Eventtrainer_->Fill("B", "dRLep", dRLep_tt);
                //Eventtrainer_->Fill("B", "fnjetW", fnjetW_tt);
                //Eventtrainer_->Fill("B", "LepFlavor", LepFlavor_tt);
                //Eventtrainer_->Fill("B", "nLep", nLep_tt);
                Eventtrainer_->Fill("B", "dRbb", dRbb_tt);
                Eventtrainer_->Fill("B", "HTb", HTb_tt);
                Eventtrainer_->Fill("B", "HTRat", HTRat_tt);
                Eventtrainer_->Fill("B", "HTH", HTH_tt);
                Eventtrainer_->Fill("B", "nLtags", nLtags_tt);
                Eventtrainer_->Fill("B", "nMtags", nMtags_tt);
                //Eventtrainer_->Fill("B", "nTtags", nTtags_tt);
                Eventtrainer_->Fill("B", "nJets", nJets_tt);
                Eventtrainer_->Fill("B", "Jet3Pt", Jet3Pt_tt);
                Eventtrainer_->Fill("B", "Jet4Pt", Jet4Pt_tt);
                Eventtrainer_->Fill("B", "HT2M", HT2M_tt);
                Eventtrainer_->Fill("B", "EventSph", EventSph_tt);
                //Eventtrainer_->Fill("B", "EventCen", EventCen_tt);
                //Eventtrainer_->Fill("B", "DiLepSph", DiLepSph_tt);
                //Eventtrainer_->Fill("B", "DiLepCen", DiLepCen_tt);
                //Eventtrainer_->Fill("B", "TopDiLepSph", TopDiLepSph_tt);
                //Eventtrainer_->Fill("B", "TopDiLepCen", TopDiLepCen_tt);
            }
            bbit = l + 1;
        }
        // } //std::string SplitMode, std::string CutsS, int nTrainS, int nTestS, std::string CutsB, int nTrainB, int nTestB, std::string postfix, bool nlo
        if(Muon && Electron && !Combined) {
            Eventtrainer_->TrainMVA("Random", "", 0, 0, "", 0, 0, "_MuEl13thFeb2018_13TeVHadTop", false);
        } else if(Muon && !Electron && !Combined) {
            Eventtrainer_->TrainMVA("Random", "", 0, 0, "", 0, 0, "_MuMu13thFeb2018_13TeVHadTop", false);
        } else if(!Muon && Electron && !Combined) {
            Eventtrainer_->TrainMVA("Random", "", 0, 0, "", 0, 0, "_ElEl13thFeb2018_13TeVHadTop", false);
        } else if(!Muon && !Electron && Combined) {
            Eventtrainer_->TrainMVA("Random", "", 0, 0, "", 0, 0, "_DilepCombined13thFeb2018_13TeVHadTop", false);
        }
        cout << "MVA Trained!" << endl;
        delete Eventtrainer_;
    }
    if(eval) {
        // if(Combined) {
        //    cerr << "Combined channel not valid for evaluation" << endl;
        //    return 0;
        //}

        vector<string> MVAvars;
        string MVApostfix;

        MVAvars.push_back("nJets");
        MVAvars.push_back("topness");
        MVAvars.push_back("HTb");
        MVAvars.push_back("HT2M");
        MVAvars.push_back("HTH");
        MVAvars.push_back("EventSph");
        MVAvars.push_back("HTRat");
        MVAvars.push_back("leadLepPt");
        MVAvars.push_back("leadLepEta");
        MVAvars.push_back("dRLep");
        //MVAvars.push_back("fnjetW");
        //MVAvars.push_back("LepFlavor");
        //MVAvars.push_back("nLep");
        MVAvars.push_back("dRbb");
        MVAvars.push_back("nLtags");
        MVAvars.push_back("nMtags");
        //MVAvars.push_back("nTtags");
        MVAvars.push_back("Jet3Pt");
        MVAvars.push_back("Jet4Pt");
        //MVAvars.push_back("EventCen");
        //MVAvars.push_back("DiLepSph");
        //MVAvars.push_back("DiLepCen");
        //MVAvars.push_back("TopDiLepSph");
        //MVAvars.push_back("TopDiLepCen");

        MVAComputer* Eventcomputer_;
        if(Muon && Electron) {
            if(combine_eval) {
                MVApostfix = "_DilepCombined13thFeb2018_13TeVHadTop";
                Eventcomputer_ = new MVAComputer("BDT", "MVA/MasterMVA_DiLep_Combined_13thFeb2018_13TeVHadTop.root",
                    "MasterMVA_DiLep_Combined_13thFeb2018_13TeVHadTop", MVAvars, MVApostfix.c_str());
            } else {
                MVApostfix = "_MuEl13thFeb2018_13TeVHadTop";
                Eventcomputer_ = new MVAComputer("BDT", "MVA/MasterMVA_MuEl_13thFeb2018_13TeVHadTop.root",
                    "MasterMVA_MuEl_13thFeb2018_13TeVHadTop", MVAvars, MVApostfix.c_str());
            }
        } else if(Muon && !Electron) {
            if(combine_eval) {
                MVApostfix = "_DilepCombined13thFeb2018_13TeVHadTop";
                Eventcomputer_ = new MVAComputer("BDT", "MVA/MasterMVA_DiLep_Combined_13thFeb2018_13TeVHadTop.root",
                    "MasterMVA_DiLep_Combined_13thFeb2018_13TeVHadTop", MVAvars, MVApostfix.c_str());
            } else {
                MVApostfix = "_MuMu13thFeb2018_13TeVHadTop";
                Eventcomputer_ = new MVAComputer("BDT", "MVA/MasterMVA_MuMu_13thFeb2018_13TeVHadTop.root",
                    "MasterMVA_MuMu_13thFeb2018_13TeVHadTop", MVAvars, MVApostfix.c_str());
            }
        } else if(!Muon && Electron) {
            if(combine_eval) {
                MVApostfix = "_DilepCombined13thFeb2018_13TeVHadTop";
                Eventcomputer_ = new MVAComputer("BDT", "MVA/MasterMVA_DiLep_Combined_13thFeb2018_13TeVHadTop.root",
                    "MasterMVA_DiLep_Combined_13thFeb2018_13TeVHadTop", MVAvars, MVApostfix.c_str());
            } else {
                MVApostfix = "_ElEl13thFeb2018_13TeVHadTop";
                Eventcomputer_ = new MVAComputer("BDT", "MVA/MasterMVA_ElEl_13thFeb2018_13TeVHadTop.root",
                    "MasterMVA_ElEl_13thFeb2018_13TeVHadTop", MVAvars, MVApostfix.c_str());
            }
        } else if(!Muon && !Electron && Combined) {
            MVApostfix = "_DilepCombined13thFeb2018_13TeVHadTop";
            Eventcomputer_ = new MVAComputer("BDT", "MVA/MasterMVA_DiLep_Combined_13thFeb2018_13TeVHadTop.root",
                "MasterMVA_DiLep_Combined_13thFeb2018_13TeVHadTop", MVAvars, MVApostfix.c_str());
        }

        cout << " Initialized Eventcomputer_" << endl;


        string filepath_data = "Craneens_Comb/Data_Run2_TopTree_Study.root";
        string filepath_tttt = "Craneens_Comb/NP_overlay_ttttNLO_Run2_TopTree_Study.root";
        string filepath_ttttJESUp = "Craneens_Comb/ttttNLO_JESUp_Run2_TopTree_Study.root";
	string filepath_ttttJESDown = "Craneens_Comb/ttttNLO_JESDown_Run2_TopTree_Study.root";
	string filepath_ttttJERUp = "Craneens_Comb/ttttNLO_JERUp_Run2_TopTree_Study.root";
	string filepath_ttttJERDown = "Craneens_Comb/ttttNLO_JERDown_Run2_TopTree_Study.root";
        string filepath_ttttISRUp = "Craneens_Comb/ttttISRUp_Run2_TopTree_Study.root";
        string filepath_ttttISRDown = "Craneens_Comb/ttttISRDown_Run2_TopTree_Study.root";
        string filepath_ttttFSRUp = "Craneens_Comb/ttttFSRUp_Run2_TopTree_Study.root";
        string filepath_ttttFSRDown = "Craneens_Comb/ttttFSRDown_Run2_TopTree_Study.root";

        string ttttNLO_SubTotalPileUpUp = "Craneens_Comb/ttttNLO_SubTotalPileUpUp_Run2_TopTree_Study.root";
        string ttttNLO_SubTotalPileUpDown = "Craneens_Comb/ttttNLO_SubTotalPileUpDown_Run2_TopTree_Study.root";
        string ttttNLO_SubTotalRelativeUp = "Craneens_Comb/ttttNLO_SubTotalRelativeUp_Run2_TopTree_Study.root";
        string ttttNLO_SubTotalRelativeDown = "Craneens_Comb/ttttNLO_SubTotalRelativeDown_Run2_TopTree_Study.root";
        string ttttNLO_SubTotalPtUp = "Craneens_Comb/ttttNLO_SubTotalPtUp_Run2_TopTree_Study.root";
        string ttttNLO_SubTotalPtDown = "Craneens_Comb/ttttNLO_SubTotalPtDown_Run2_TopTree_Study.root";
        string ttttNLO_SubTotalScaleUp = "Craneens_Comb/ttttNLO_SubTotalScaleUp_Run2_TopTree_Study.root";
        string ttttNLO_SubTotalScaleDown = "Craneens_Comb/ttttNLO_SubTotalScaleDown_Run2_TopTree_Study.root";
        string ttttNLO_SubTotalFlavorUp = "Craneens_Comb/ttttNLO_SubTotalFlavorUp_Run2_TopTree_Study.root";
        string ttttNLO_SubTotalFlavorDown = "Craneens_Comb/ttttNLO_SubTotalFlavorDown_Run2_TopTree_Study.root";
        string TTJets_SubTotalPileUpUp = "Craneens_Comb/TTJets_SubTotalPileUpUp_Run2_TopTree_Study.root";
        string TTJets_SubTotalPileUpDown = "Craneens_Comb/TTJets_SubTotalPileUpDown_Run2_TopTree_Study.root";
        string TTJets_SubTotalRelativeUp = "Craneens_Comb/TTJets_SubTotalRelativeUp_Run2_TopTree_Study.root";
        string TTJets_SubTotalRelativeDown = "Craneens_Comb/TTJets_SubTotalRelativeDown_Run2_TopTree_Study.root";
        string TTJets_SubTotalPtUp = "Craneens_Comb/TTJets_SubTotalPtUp_Run2_TopTree_Study.root";
        string TTJets_SubTotalPtDown = "Craneens_Comb/TTJets_SubTotalPtDown_Run2_TopTree_Study.root";
        string TTJets_SubTotalScaleUp = "Craneens_Comb/TTJets_SubTotalScaleUp_Run2_TopTree_Study.root";
        string TTJets_SubTotalScaleDown = "Craneens_Comb/TTJets_SubTotalScaleDown_Run2_TopTree_Study.root";
        string TTJets_SubTotalFlavorUp = "Craneens_Comb/TTJets_SubTotalFlavorUp_Run2_TopTree_Study.root";
        string TTJets_SubTotalFlavorDown = "Craneens_Comb/TTJets_SubTotalFlavorDown_Run2_TopTree_Study.root";

        string filepath_ttbarPowheg = "Craneens_Comb/TTJetsPowheg_Run2_TopTree_Study.root";
        string filepath_ttbarPowhegJESUp = "Craneens_Comb/TTJetsPowheg_JESUp_Run2_TopTree_Study.root";
        string filepath_ttbarPowhegJESDown = "Craneens_Comb/TTJetsPowheg_JESDown_Run2_TopTree_Study.root";
        string filepath_ttbarPowhegJERUp = "Craneens_Comb/TTJetsPowheg_JERUp_Run2_TopTree_Study.root";
        string filepath_ttbarPowhegJERDown = "Craneens_Comb/TTJetsPowheg_JERDown_Run2_TopTree_Study.root";
        string filepath_ttbarUEUp = "Craneens_Comb/TTUEUp_Run2_TopTree_Study.root";
        string filepath_ttbarUEDown = "Craneens_Comb/TTUEDown_Run2_TopTree_Study.root";
        string filepath_TTISRUp = "Craneens_Comb/TTISRUp_Run2_TopTree_Study.root";
        string filepath_TTISRDown = "Craneens_Comb/TTISRDown_Run2_TopTree_Study.root";
        string filepath_TTFSRUp = "Craneens_Comb/TTFSRUp_Run2_TopTree_Study.root";
        string filepath_TTFSRDown = "Craneens_Comb/TTFSRDown_Run2_TopTree_Study.root";

        string filepath_tW = "Craneens_Comb/ST_tW_Run2_TopTree_Study.root";
        string filepath_DY = "Craneens_Comb/DYJets_Run2_TopTree_Study.root";
        string filepath_tth = "Craneens_Comb/Rare1TTH_Run2_TopTree_Study.root";
        string filepath_ttw = "Craneens_Comb/Rare2TTW_Run2_TopTree_Study.root";
        string filepath_ttz = "Craneens_Comb/Rare1TTZ_Run2_TopTree_Study.root";
        string filepath_ttwz = "Craneens_Comb/Rare2TTWZ_Run2_TopTree_Study.root";
        string filepath_ttzz = "Craneens_Comb/Rare2TTZZ_Run2_TopTree_Study.root";
        string filepath_ttzh = "Craneens_Comb/Rare2TTZH_Run2_TopTree_Study.root";
        string filepath_tthh = "Craneens_Comb/Rare2TTHH_Run2_TopTree_Study.root";
        string filepath_tttw = "Craneens_Comb/Rare2TTTW_Run2_TopTree_Study.root";
        string filepath_tttj = "Craneens_Comb/Rare2TTTJ_Run2_TopTree_Study.root";
        string filepath_zz = "Craneens_Comb/EWZZ_Run2_TopTree_Study.root";
        string filepath_wz = "Craneens_Comb/EWWZ_Run2_TopTree_Study.root";

        string powhegnew = "Craneens_Comb/TTJetsPowheg_new_Run2_TopTree_Study.root";


        vector<TFile*> files;


        files.push_back(TFile::Open(filepath_data.c_str(), "UPDATE"));
/*        files.push_back(TFile::Open(filepath_tttt.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttttJESUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttttJESDown.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttttJERUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttttJERDown.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttttISRUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttttISRDown.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttttFSRUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttttFSRDown.c_str(), "UPDATE"));

        files.push_back(TFile::Open(ttttNLO_SubTotalPileUpUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(ttttNLO_SubTotalPileUpDown.c_str(), "UPDATE"));
        files.push_back(TFile::Open(ttttNLO_SubTotalRelativeUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(ttttNLO_SubTotalRelativeDown.c_str(), "UPDATE"));
        files.push_back(TFile::Open(ttttNLO_SubTotalPtUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(ttttNLO_SubTotalPtDown.c_str(), "UPDATE"));
        files.push_back(TFile::Open(ttttNLO_SubTotalScaleUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(ttttNLO_SubTotalScaleDown.c_str(), "UPDATE"));
        files.push_back(TFile::Open(ttttNLO_SubTotalFlavorUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(ttttNLO_SubTotalFlavorDown.c_str(), "UPDATE"));
        files.push_back(TFile::Open(TTJets_SubTotalPileUpUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(TTJets_SubTotalPileUpDown.c_str(), "UPDATE"));
        files.push_back(TFile::Open(TTJets_SubTotalRelativeUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(TTJets_SubTotalRelativeDown.c_str(), "UPDATE"));
        files.push_back(TFile::Open(TTJets_SubTotalPtUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(TTJets_SubTotalPtDown.c_str(), "UPDATE"));
        files.push_back(TFile::Open(TTJets_SubTotalScaleUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(TTJets_SubTotalScaleDown.c_str(), "UPDATE"));
        files.push_back(TFile::Open(TTJets_SubTotalFlavorUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(TTJets_SubTotalFlavorDown.c_str(), "UPDATE"));

        files.push_back(TFile::Open(filepath_ttbarPowheg.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttbarPowhegJESUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttbarPowhegJESDown.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttbarPowhegJERUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttbarPowhegJERDown.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttbarUEUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttbarUEDown.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_TTISRUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_TTISRDown.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_TTFSRUp.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_TTFSRDown.c_str(), "UPDATE"));

        files.push_back(TFile::Open(filepath_tW.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_DY.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_tth.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttw.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttz.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttwz.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttzz.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_ttzh.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_tthh.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_tttw.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_tttj.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_zz.c_str(), "UPDATE"));
        files.push_back(TFile::Open(filepath_wz.c_str(), "UPDATE"));

        files.push_back(TFile::Open(powhegnew.c_str(), "UPDATE"));
*/

        for(int i = 0; i < files.size(); i++) { // loop through the samples
            TNtuple* tup = (TNtuple*)files[i]->Get(nTuplename.c_str());
            cout << "Sample: " << files[i]->GetPath() << endl;
            files[i]->cd();

            float topness, leadLepPt, leadLepEta, HTH, HTRat, HTb, nLtags, nMtags, nTtags, nJets, HT2M, EventSph, weight,
                dRLep, fnjetW, nLep, LepFlavor, dRbb, Jet3Pt, Jet4Pt;
            float BDTScore;

            tup->SetBranchAddress("GenWeight", &weight);
            tup->SetBranchAddress("topness", &topness);
            tup->SetBranchAddress("LeadingLepPt", &leadLepPt);
            tup->SetBranchAddress("LeadingLepEta", &leadLepEta);
            tup->SetBranchAddress("dRLep", &dRLep);
            //tup->SetBranchAddress("fnjetW", &fnjetW);
            tup->SetBranchAddress("LepFlavor", &LepFlavor);
            tup->SetBranchAddress("nLep", &nLep);
            tup->SetBranchAddress("dRbb", &dRbb);
            tup->SetBranchAddress("HTb", &HTb);
            tup->SetBranchAddress("HTH", &HTH);
            tup->SetBranchAddress("HTRat", &HTRat);
            tup->SetBranchAddress("nLtags", &nLtags);
            tup->SetBranchAddress("nMtags", &nMtags);
            tup->SetBranchAddress("nTtags", &nTtags);
            tup->SetBranchAddress("nJets", &nJets);
            tup->SetBranchAddress("HT2M", &HT2M);
            tup->SetBranchAddress("3rdJetPt", &Jet3Pt);
            tup->SetBranchAddress("4thJetPt", &Jet4Pt);
            tup->SetBranchAddress("EventSph", &EventSph);

            string branchName = "BDT" + MVApostfix; // name for the branch of the new BDT discriminant
            string branchDescrip = chan + "_" + branchName;
            TNtuple* output = new TNtuple(branchDescrip.c_str(), branchDescrip.c_str(), branchName.c_str());

            for(int k = 0; k < tup->GetEntries(); k++) { // loop through entries in the tree
                tup->GetEntry(k);

                if(nJets >= 4) { // fill values to compute MVAVal
                    Eventcomputer_->FillVar("topness", topness);
                    Eventcomputer_->FillVar("leadLepPt", leadLepPt);
                    Eventcomputer_->FillVar("leadLepEta", leadLepEta);
                    Eventcomputer_->FillVar("dRLep", dRLep);
                    //Eventcomputer_->FillVar("fnjetW", fnjetW);
                    //Eventcomputer_->FillVar("LepFlavor", LepFlavor);
                    //Eventcomputer_->FillVar("nLep", nLep);
                    Eventcomputer_->FillVar("dRbb", dRbb);
                    Eventcomputer_->FillVar("HTH", HTH);
                    Eventcomputer_->FillVar("HTRat", HTRat);
                    Eventcomputer_->FillVar("HTb", HTb);
                    Eventcomputer_->FillVar("nLtags", nLtags);
                    Eventcomputer_->FillVar("nMtags", nMtags);
                    //Eventcomputer_->FillVar("nTtags", nTtags);
                    Eventcomputer_->FillVar("nJets", nJets);
                    Eventcomputer_->FillVar("Jet3Pt", Jet3Pt);
                    Eventcomputer_->FillVar("Jet4Pt", Jet4Pt);
                    Eventcomputer_->FillVar("HT2M", HT2M);
                    Eventcomputer_->FillVar("EventSph", EventSph);
                    //Eventcomputer_->FillVar("EventCen", tCen);
                    //Eventcomputer_->FillVar("DiLepSph", dSph);
                    //Eventcomputer_->FillVar("DiLepCen", dCen);
                    //Eventcomputer_->FillVar("TopDiLepSph", tdSph);
                    //Eventcomputer_->FillVar("TopDiLepCen", tdCen);

                    std::map<std::string, Float_t> MVAVals = Eventcomputer_->GetMVAValues();

                    for(std::map<std::string, Float_t>::const_iterator it = MVAVals.begin(); it != MVAVals.end();
                        ++it) {

                        //  cout <<"MVA Method : "<< it->first    <<" Score : "<< it->second <<endl;
                        BDTScore = it->second;
                    }
                }
                output->Fill(BDTScore);
            }
            output->Write();
            tup->AddFriend(output);
            tup->Write("", TObject::kWriteDelete);
            files[i]->Close();
        }
        delete Eventcomputer_;
    }
}
