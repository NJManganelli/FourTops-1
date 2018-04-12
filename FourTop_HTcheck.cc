////////////////////////////////////////////////////////////////////////////////////
////         Analysis code for search for Four Top Production.                  ////
////////////////////////////////////////////////////////////////////////////////////

// ttbar @ NLO 13 TeV:
// all-had ->679 * .46 = 312.34
// semi-lep ->679 *.45 = 305.55
// di-lep-> 679* .09 = 61.11

// ttbar @ NNLO 8 TeV:
// all-had -> 245.8 * .46 = 113.068
// semi-lep-> 245.8 * .45 = 110.61
// di-lep ->  245.8 * .09 = 22.122

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

#include "TopTreeProducer/interface/TRootRun.h"
#include "TopTreeProducer/interface/TRootEvent.h"
#include "TopTreeAnalysisBase/Selection/interface/Run2Selection.h"
#include "TopTreeAnalysisBase/Content/interface/AnalysisEnvironment.h"
#include "TopTreeAnalysisBase/Content/interface/Dataset.h"
#include "TopTreeAnalysisBase/Tools/interface/JetTools.h"
#include "TopTreeAnalysisBase/Tools/interface/BTagWeightTools.h"
#include "TopTreeAnalysisBase/Tools/interface/BTagCalibrationStandalone.h"
#include "TopTreeAnalysisBase/Tools/interface/JetCombiner.h"
//#include "TopTreeAnalysisBase/Tools/interface/MVATrainer.h"
//#include "TopTreeAnalysisBase/Tools/interface/MVAComputer.h"
#include "TopTreeAnalysisBase/Tools/interface/TopologyWorker.h"
//#include "TopTreeAnalysisBase/Tools/interface/PlottingTools.h"
//#include "TopTreeAnalysisBase/Tools/interface/MultiSamplePlot.h"
#include "TopTreeAnalysisBase/Tools/interface/Trigger.h"
#include "TopTreeAnalysisBase/Tools/interface/TTreeLoader.h"
#include "TopTreeAnalysisBase/Tools/interface/LeptonTools.h"
#include "TopTreeAnalysisBase/Tools/interface/AnalysisEnvironmentLoader.h"
#include "TopTreeAnalysisBase/Reconstruction/interface/JetCorrectorParameters.h"
#include "TopTreeAnalysisBase/Reconstruction/interface/JetCorrectionUncertainty.h"
#include "TopTreeAnalysisBase/Reconstruction/interface/MakeBinning.h"
#include "TopTreeAnalysisBase/Reconstruction/interface/MEzCalculator.h"
#include "TopTreeAnalysisBase/Reconstruction/interface/TTreeObservables.h"
#include "TopTreeAnalysisBase/MCInformation/interface/LumiReWeighting.h"
#include "TopTreeAnalysisBase/MCInformation/interface/JetPartonMatching.h"

using namespace std;
using namespace TopTree;
using namespace reweight;

bool split_ttbar = false;
float topness;

pair<float, vector<unsigned int> > MVAvals1;
pair<float, vector<unsigned int> > MVAvals2;
pair<float, vector<unsigned int> > MVAvals2ndPass;
pair<float, vector<unsigned int> > MVAvals3rdPass;

int nMVASuccesses = 0;
int nMatchedEvents = 0;

map<string, TH1F*> histo1D;
map<string, TH2F*> histo2D;
map<string, TProfile*> histoProfile;

struct HighestCVSBtag {
    bool operator()(TRootJet* j1, TRootJet* j2) const
    {
        return j1->btag_combinedInclusiveSecondaryVertexV2BJetTags() > j2->btag_combinedInclusiveSecondaryVertexV2BJetTags();
    }
};

// To cout the Px, Py, Pz, E and Pt of objects
int Factorial(int N);
float Sphericity(vector<TLorentzVector> parts);
float Centrality(vector<TLorentzVector> parts);
float ElectronRelIso(TRootElectron* el, float rho);
float MuonRelIso(TRootMuon* mu);
float PythiaTune(int jets);

int main(int argc, char* argv[])
{

    // Checking Passed Arguments to ensure proper execution of MACRO
    if(argc < 12) {
        std::cerr << "TOO FEW INPUTs FROM XMLFILE.  CHECK XML INPUT FROM SCRIPT.  " << argc << " ARGUMENTS HAVE BEEN PASSED." << std::endl;
        return 1;
    }
    // Placing arguments in properly typed variables for Dataset creation
    const string dName = argv[1];
    const string dTitle = argv[2];
    const int color = strtol(argv[4], NULL, 10);
    const int ls = strtol(argv[5], NULL, 10);
    const int lw = strtol(argv[6], NULL, 10);
    const float normf = strtod(argv[7], NULL);
    const float EqLumi = strtod(argv[8], NULL);
    const float xSect = strtod(argv[9], NULL);
    const float PreselEff = strtod(argv[10], NULL);
    vector<string> vecfileNames;
    for(int args = 11; args < argc; args++) {
        vecfileNames.push_back(argv[args]);
    }
    cout << "---Dataset accepted from command line---" << endl;
    cout << "Dataset Name: " << dName << endl;
    cout << "Dataset Title: " << dTitle << endl;
    cout << "Dataset color: " << color << endl;
    cout << "Dataset ls: " << ls << endl;
    cout << "Dataset lw: " << lw << endl;
    cout << "Dataset normf: " << normf << endl;
    cout << "Dataset EqLumi: " << EqLumi << endl;
    cout << "Dataset xSect: " << xSect << endl;
    for(int files = 0; files < vecfileNames.size(); files++) {
        cout << "Dataset File Names: " << vecfileNames[files] << endl;
    }
    cout << "----------------------------------------------------------------------" << endl;

    int passed = 0;
    int negWeights = 0;
    float weightCount = 0.0;
    int eventCount = 0, trigCount = 0;
    clock_t start = clock();
    string postfix = "_Run2_TopTree_Study";
    int doJESShift = 0; // 0: off 1: minus 2: plus
    cout << "doJESShift: " << doJESShift << endl;
    int doJERShift = 0; // 0: off (except nominal scalefactor for jer) 1: minus 2: plus
    cout << "doJERShift: " << doJERShift << endl;
    int dobTagEffShift = 0; // 0: off (except nominal scalefactor for btag eff) 1: minus 2: plus
    cout << "dobTagEffShift: " << dobTagEffShift << endl;
    int domisTagEffShift = 0; // 0: off (except nominal scalefactor for mistag eff) 1: minus 2: plus
    cout << "domisTagEffShift: " << domisTagEffShift << endl;
    int mvaNegWeight = 0; // 0: Using MVA trained without neg weights 1: Using MVA trained with Neg Weights
    cout << "mvaNegWeight: " << mvaNegWeight << endl;
    if(doJESShift == 1)
        postfix = postfix + "_JESMinus";
    if(doJESShift == 2)
        postfix = postfix + "_JESPlus";
    if(doJERShift == 1)
        postfix = postfix + "_JERMinus";
    if(doJERShift == 2)
        postfix = postfix + "_JERPlus";
    if(dobTagEffShift == -1)
        postfix = postfix + "_bTagMinus";
    if(dobTagEffShift == 1)
        postfix = postfix + "_bTagPlus";
    if(domisTagEffShift == -1)
        postfix = postfix + "_misTagMinus";
    if(domisTagEffShift == 1)
        postfix = postfix + "_misTagPlus";
    if(mvaNegWeight == 1)
        postfix = postfix + "_MVANegWeight";
    
    cout << "*************************************************************" << endl;
    cout << " Beginning of the program for the FourTop search ! " << endl;
    cout << "*************************************************************" << endl;


    ///////////////////////////////////////
    //      Configuration                //
    ///////////////////////////////////////

    string channelpostfix = "";
    string MVAmethod = "BDT";  // MVAmethod to be used to get the good jet combi calculation (not for training! this is chosen in the jetcombiner class)
    float Luminosity; // pb^-1 

    bool debug = false;
    bool dilepton = true;
    bool Muon = false;
    bool Electron = false;
    bool HadTopOn = true;
    bool EventBDTOn = true;
    bool TrainMVA = false; // If false, the previously trained MVA will be used to calculate stuff
    bool bTagReweight = false;
    bool bTagCSVReweight = true;
    bool bLeptonSF = true;
    bool applyJER = true;
    bool applyJEC = true;
    bool JERNom = false;
    bool JERUp = false;
    bool JERDown = false;
    bool JESUp = false;
    bool JESDown = false;
    bool fillingbTagHistos = false;
    bool verbose = false;

    if(dName.find("MuEl") != std::string::npos) {
        Muon = true;
        Electron = true;
    } else if(dName.find("MuMu") != std::string::npos) {
        Muon = true;
        Electron = false;
    } else if(dName.find("ElEl") != std::string::npos) {
        Muon = false;
        Electron = true;
    } else
        cout << "Boolean setting by name failed" << endl;

    if(Muon && Electron && dilepton) {
        cout << " --> Using the Muon-Electron channel..." << endl;
        channelpostfix = "_MuEl";
    } else if(Muon && !Electron && dilepton) {
        cout << " --> Using the Muon-Muon channel..." << endl;
        channelpostfix = "_MuMu";
    } else if(!Muon && Electron && dilepton) {
        cout << " --> Using the Electron-Electron channel..." << endl;
        channelpostfix = "_ElEl";
    } else {
        cerr << "Correct Di-lepton Channel not selected." << endl;
        exit(1);
    }

    //////////////////////////////////
    //  Set up AnalysisEnvironment  //
    //////////////////////////////////

    AnalysisEnvironment anaEnv;
    cout << "Creating environment ..." << endl;
    anaEnv.PrimaryVertexCollection = "PrimaryVertex";
    anaEnv.JetCollection = "PFJets_slimmedJets";
    anaEnv.FatJetCollection = "FatJets_slimmedJetsAK8";
    anaEnv.METCollection = "PFMET_slimmedMETs";
    anaEnv.MuonCollection = "Muons_slimmedMuons";
    anaEnv.ElectronCollection = "Electrons_selectedElectrons";
    anaEnv.GenJetCollection = "GenJets_slimmedGenJets";
    //anaEnv.TrackMETCollection = "";
    //anaEnv.GenEventCollection = "GenEvent";
    anaEnv.NPGenEventCollection = "NPGenEvent";
    anaEnv.MCParticlesCollection = "MCParticles";
    anaEnv.loadFatJetCollection = true;
    anaEnv.loadGenJetCollection = true;
    //anaEnv.loadTrackMETCollection = true;
    //anaEnv.loadGenEventCollection = true;
    anaEnv.loadNPGenEventCollection = false;
    anaEnv.loadMCParticles = true;
    anaEnv.JetType = 2;
    anaEnv.METType = 2;
    //anaEnv.Verbose;

    ////////////////////////////////
    //  Load datasets             //
    ////////////////////////////////

    TTreeLoader treeLoader;
    vector<Dataset*> datasets;
    cout << "Creating Dataset ..." << endl;
    Dataset* theDataset = new Dataset(dName, dTitle, true, color, ls, lw, normf, xSect, vecfileNames);
    theDataset->SetEquivalentLuminosity(EqLumi);
    datasets.push_back(theDataset);
    string dataSetName = theDataset->Name();

    bool isData = false;
    if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos || dataSetName.find("DATA") != string::npos) {
        isData = true;
    }
    
    Luminosity = 35822.4374055;

    // vector of objects
    cout << "Variable declaration ..." << endl;
    vector<TRootVertex*> vertex;
    vector<TRootMuon*> init_muons;
    vector<TRootElectron*> init_electrons;
    vector<TRootJet*> init_jets;
    vector<TRootJet*> init_fatjets;
    vector<TRootMET*> mets;
    vector<TRootGenJet*> genjets;
    vector<TRootMCParticle*> mcpart;

    // Global variable
    TRootEvent* event = 0;

    // Plots
    string pathPNG = "OUTPUT/FourTop" + postfix + channelpostfix;
    mkdir(pathPNG.c_str(), 0777);
    cout << "Making directory :" << pathPNG << endl;


    /////////////////////////////////
    // Loop on datasets
    /////////////////////////////////

    cout << "Looping over datasets ... " << datasets.size() << " datasets !" << endl;

    for(int d = 0; d < datasets.size(); d++) {
        cout << "Loading Dataset" << endl;
        treeLoader.LoadDataset(datasets[d], anaEnv); // open files and load dataset
        string previousFilename = "";
        int iFile = -1;
        bool nlo = false;
        dataSetName = datasets[d]->Name();


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
        string channel_dir = "OutCraneens" + channelpostfix;
        string date_dir = channel_dir + "/OutCraneens" + date_str + "/";
        int mkdirstatus = mkdir(channel_dir.c_str(), 0777);
        mkdirstatus = mkdir(date_dir.c_str(), 0777);

        string Ntupname = "OutCraneens" + channelpostfix + "/OutCraneens" + date_str + "/" + dataSetName + postfix + ".root";
        string Cuttupname = "OutCraneens" + channelpostfix + "/Cutflow" + date_str + "/" + dataSetName + ".root";
        string Ntuptitle = "Craneen_" + channelpostfix;
        string cutTuptitle = "Craneen_" + channelpostfix + "_CutFlow";

        TFile* tupfile = new TFile(Ntupname.c_str(), "RECREATE");
        TNtuple* tup = new TNtuple(Ntuptitle.c_str(), Ntuptitle.c_str(), "genHT:n_genjets:n_genleps");
        /*
        TTree *tree = new TTree(("Tree"+channelpostfix).c_str(),("Tree"+channelpostfix).c_str());
        long long EventID[3];
        TLorentzVector *TLVlep1=new TLorentzVector(), *TLVlep2=new TLorentzVector(), *TLVjet1=new TLorentzVector(),
                       *TLVjet2=new TLorentzVector(), *TLVjet3=new TLorentzVector(), *TLVjet4=new TLorentzVector();
        tree->Branch("EventID",&EventID,"EvenntID/lld");
        tree->Branch("TLVlep1","TLorentzVector",&TLVlep1);
        tree->Branch("TLVlep2","TLorentzVector",&TLVlep2);
        tree->Branch("TLVjet1","TLorentzVector",&TLVjet1);
        tree->Branch("TLVjet2","TLorentzVector",&TLVjet2);
        tree->Branch("TLVjet3","TLorentzVector",&TLVjet3);
        tree->Branch("TLVjet4","TLorentzVector",&TLVjet4);
        */
        //TFile* cuttupfile = new TFile(Cuttupname.c_str(), "RECREATE");
        //TNtuple* cuttup = new TNtuple(cutTuptitle.c_str(), cutTuptitle.c_str(),
        //    "initevent:trigger:isGoodPV:Lep1:Lep2:nJets2:nJets3:nJets4:nTags:HT");


        //////////////////////////////////////////////////
        // Loop on events
        //////////////////////////////////////////////////

        cout << "First try to read into dataset::potential tech. bugz::" << endl;
        long int event_end = datasets[d]->NofEvtsToRunOver();
        cout << "Number of total events in dataset = " << event_end << endl;

        int previousRun = -1;
        int start = 0;

        if(debug) event_end = 10; //artifical ending for debug
        cout << "Looping over events ..." << endl;
        cout << "Will run over " << (event_end - start) << " events..." << endl;
        cout << "Starting event ==== " << start << endl;
        if(event_end < 0) {
            cout << "Starting event larger than number of events.  Exiting." << endl;
            return 1;
        }

        TRootRun* runInfos = new TRootRun();
        datasets[d]->runTree()->SetBranchStatus("runInfos*", 1);
        datasets[d]->runTree()->SetBranchAddress("runInfos", &runInfos);


        //////////////////////////////////////
        // Begin Event Loop
        //////////////////////////////////////

        for(long int ievt = 0; ievt < event_end; ievt++) {

            float genHT = 0.; float genLepPt = -999.;
            int n_genjets = 0; int n_genleps = 0;

            if(ievt % 10000 == 0) {
                cout << "Processing the " << ievt << "th event, time = " << ((double)clock() - start) / CLOCKS_PER_SEC << " (" << 100 * (ievt - start) / (event_end - start) << "%)" << flush << "\r" << endl;
            }

            genjets.clear();vertex.clear();init_muons.clear();init_electrons.clear();init_jets.clear();init_fatjets.clear();mets.clear();
            event = treeLoader.LoadEvent(ievt, vertex, init_muons, init_electrons, init_jets, init_fatjets, mets, debug); // load event
            if(!isData) genjets = treeLoader.LoadGenJet(ievt, false);
            mcpart = treeLoader.LoadMCPart(ievt, false);

            datasets[d]->eventTree()->LoadTree(ievt);
            string currentFilename = datasets[d]->eventTree()->GetFile()->GetName();
            if(previousFilename != currentFilename) {
                previousFilename = currentFilename;
                iFile++;
                cout << "File changed!!! => " << currentFilename << endl;
            }

            eventCount++;

            long int runId    = event->runId();
            long int eventId     = event->eventId();
            long int lumiBlockId = event->lumiBlockId();

            for(int gj = 0; gj < genjets.size(); gj++) {
                if(genjets[gj]->Pt()>30 && abs(genjets[gj]->Eta())<2.4)
                    genHT += genjets[gj]->Pt();
                if(genjets[gj]->Pt()>30)
                    n_genjets++;
            }

            
            for(int mc = 0; mc < mcpart.size(); mc++) {

                if(
                    (
                        ( mcpart[mc]->status()==1 && (fabs(mcpart[mc]->type())==11||fabs(mcpart[mc]->type())==13) ) ||
                        ( mcpart[mc]->status()==2 && fabs(mcpart[mc]->type())==15 )
                    )
                    && fabs(mcpart[mc]->grannyType())==6
                    && fabs(mcpart[mc]->motherType())==24
                ) {
                    n_genleps++;
                }

            }


            tup->Fill(genHT,n_genjets,n_genleps);



        } // End Loop on Events

        tupfile->cd();
        tup->Write();
        tupfile->Close();

        cout << "n events passing filter     = " << eventCount << endl;

        treeLoader.UnLoadDataset(); // important: free memory
    } // End Loop on Datasets

    cout << "Writing outputs to the files ..." << endl;

    cout << "It took us " << ((double)clock() - start) / CLOCKS_PER_SEC << "s to run the program" << endl;
    cout << "********************************************" << endl;
    cout << "           End of the program !!            " << endl;
    cout << "********************************************" << endl;

    return 0;
}

int Factorial(int N = 1)
{
    int fact = 1;
    for(int i = 1; i <= N; i++)
        fact = fact * i; // OR fact *= i;
    return fact;
}

