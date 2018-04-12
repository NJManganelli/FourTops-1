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

#include "TopTreeAnalysisBase/Tools/interface/TopologyWorker.h"

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

    int passed = 0, trigCount = 0, eventCount = 0;
    clock_t start = clock();
    string postfix = "_Run2_TopTree_Study";

    
    cout << "*************************************************************" << endl;
    cout << " Beginning of the program for the FourTop search ! " << endl;
    cout << "*************************************************************" << endl;


    ///////////////////////////////////////
    //      Configuration                //
    ///////////////////////////////////////

    string channelpostfix = "";
    string MVAmethod = "BDT";
    float Luminosity = 35822.4374055;

    bool debug = false;
    bool dilepton = true;
    bool Muon = false;
    bool Electron = false;
    bool applyJEC = true;
    bool TrainMVA = false;
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
    anaEnv.NPGenEventCollection = "NPGenEvent";
    anaEnv.MCParticlesCollection = "MCParticles";
    
    anaEnv.loadFatJetCollection = true;
    anaEnv.loadGenJetCollection = true;
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
    

    /////////////////////////////
    //   Initialize Trigger    //
    /////////////////////////////

    Trigger* trigger_mumu = new Trigger(1, 0, 0, 1,0,0,0);  // mu , el, single, double, tri, met, jet
    Trigger* trigger_muel = new Trigger(1, 1, 0, 1,0,0,0);
    Trigger* trigger_elel = new Trigger(0, 1, 0, 1,0,0,0);
    Trigger* trigger_mu = new Trigger(1, 0, 1, 0,0,0,0);
    Trigger* trigger_el = new Trigger(0, 1, 1, 0,0,0,0);


    //////////////////////////////////////////////////
    //               JEC factors                    //
    //////////////////////////////////////////////////
    cout << "Loading JEC files..." << endl;
    vector<JetCorrectorParameters> vCorrParam;
    string pathCalJEC = "../TopTreeAnalysisBase/Calibrations/JECFiles/";
    JetCorrectionUncertainty *jecUnc;

    if(dataSetName.find("Data_Run2016B")!=string::npos || dataSetName.find("Data_Run2016C")!=string::npos || dataSetName.find("Data_Run2016D")!=string::npos) {
        JetCorrectorParameters *L1JetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016BCDV4_DATA/Summer16_23Sep2016BCDV4_DATA_L1FastJet_AK4PFchs.txt");
        vCorrParam.push_back(*L1JetCorPar);
        JetCorrectorParameters *L2JetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016BCDV4_DATA/Summer16_23Sep2016BCDV4_DATA_L2Relative_AK4PFchs.txt");
        vCorrParam.push_back(*L2JetCorPar);
        JetCorrectorParameters *L3JetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016BCDV4_DATA/Summer16_23Sep2016BCDV4_DATA_L3Absolute_AK4PFchs.txt");
        vCorrParam.push_back(*L3JetCorPar);
        JetCorrectorParameters *L2L3ResJetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016BCDV4_DATA/Summer16_23Sep2016BCDV4_DATA_L2L3Residual_AK4PFchs.txt");
        vCorrParam.push_back(*L2L3ResJetCorPar);
        jecUnc = new JetCorrectionUncertainty(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016BCDV4_DATA/Summer16_23Sep2016BCDV4_DATA_Uncertainty_AK4PFchs.txt");
    } else if(dataSetName.find("Data_Run2016E")!=string::npos || dataSetName.find("Data_Run2016F")!=string::npos) {
        JetCorrectorParameters *L1JetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016EFV4_DATA/Summer16_23Sep2016EFV4_DATA_L1FastJet_AK4PFchs.txt");
        vCorrParam.push_back(*L1JetCorPar);
        JetCorrectorParameters *L2JetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016EFV4_DATA/Summer16_23Sep2016EFV4_DATA_L2Relative_AK4PFchs.txt");
        vCorrParam.push_back(*L2JetCorPar);
        JetCorrectorParameters *L3JetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016EFV4_DATA/Summer16_23Sep2016EFV4_DATA_L3Absolute_AK4PFchs.txt");
        vCorrParam.push_back(*L3JetCorPar);
        JetCorrectorParameters *L2L3ResJetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016EFV4_DATA/Summer16_23Sep2016EFV4_DATA_L2L3Residual_AK4PFchs.txt");
        vCorrParam.push_back(*L2L3ResJetCorPar);
        jecUnc = new JetCorrectionUncertainty(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016EFV4_DATA/Summer16_23Sep2016EFV4_DATA_Uncertainty_AK4PFchs.txt");
    } else if(dataSetName.find("Data_Run2016G")!=string::npos) {
        JetCorrectorParameters *L1JetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016GV4_DATA/Summer16_23Sep2016GV4_DATA_L1FastJet_AK4PFchs.txt");
        vCorrParam.push_back(*L1JetCorPar);
        JetCorrectorParameters *L2JetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016GV4_DATA/Summer16_23Sep2016GV4_DATA_L2Relative_AK4PFchs.txt");
        vCorrParam.push_back(*L2JetCorPar);
        JetCorrectorParameters *L3JetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016GV4_DATA/Summer16_23Sep2016GV4_DATA_L3Absolute_AK4PFchs.txt");
        vCorrParam.push_back(*L3JetCorPar);
        JetCorrectorParameters *L2L3ResJetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016GV4_DATA/Summer16_23Sep2016GV4_DATA_L2L3Residual_AK4PFchs.txt");
        vCorrParam.push_back(*L2L3ResJetCorPar);
        jecUnc = new JetCorrectionUncertainty(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016GV4_DATA/Summer16_23Sep2016GV4_DATA_Uncertainty_AK4PFchs.txt");
    } else if(dataSetName.find("Data_Run2016H")!=string::npos) {
        JetCorrectorParameters *L1JetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016HV4_DATA/Summer16_23Sep2016HV4_DATA_L1FastJet_AK4PFchs.txt");
        vCorrParam.push_back(*L1JetCorPar);
        JetCorrectorParameters *L2JetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016HV4_DATA/Summer16_23Sep2016HV4_DATA_L2Relative_AK4PFchs.txt");
        vCorrParam.push_back(*L2JetCorPar);
        JetCorrectorParameters *L3JetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016HV4_DATA/Summer16_23Sep2016HV4_DATA_L3Absolute_AK4PFchs.txt");
        vCorrParam.push_back(*L3JetCorPar);
        JetCorrectorParameters *L2L3ResJetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016HV4_DATA/Summer16_23Sep2016HV4_DATA_L2L3Residual_AK4PFchs.txt");
        vCorrParam.push_back(*L2L3ResJetCorPar);
        jecUnc = new JetCorrectionUncertainty(pathCalJEC+"/Summer16_23Sep2016V4_DATA/Summer16_23Sep2016HV4_DATA/Summer16_23Sep2016HV4_DATA_Uncertainty_AK4PFchs.txt");
    }

    JetTools* jetTools = new JetTools(vCorrParam, jecUnc, true);

    JetCombiner* jetCombiner = new JetCombiner(TrainMVA, Luminosity, datasets, MVAmethod, false, "", "_13TeV");
    cout << "Instantiated jet combiner ..." << endl;


    // vector of objects
    cout << "Variable declaration ..." << endl;
    vector<TRootVertex*> vertex;
    vector<TRootMuon*> init_muons;
    vector<TRootElectron*> init_electrons;
    vector<TRootJet*> init_jets;
    vector<TRootJet*> init_fatjets;
    vector<TRootMET*> mets;

    // Global variable
    TRootEvent* event = 0;


    /////////////////////////////////
    // Loop on datasets
    /////////////////////////////////

    cout << "Looping over datasets ... " << datasets.size() << " datasets !" << endl;

    for(int d = 0; d < datasets.size(); d++) {
        cout << "Loading Dataset" << endl;
        treeLoader.LoadDataset(datasets[d], anaEnv); // open files and load dataset
        string previousFilename = "";
        int iFile = -1;
        dataSetName = datasets[d]->Name();

        ///////////////////////
        // booking triggers  //
        ///////////////////////

        trigger_mumu->bookTriggers(isData,dataSetName);
        trigger_muel->bookTriggers(isData,dataSetName);
        trigger_elel->bookTriggers(isData,dataSetName);
        trigger_mu->bookTriggers(isData,dataSetName);
        trigger_el->bookTriggers(isData,dataSetName);

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
        string year_str, month_str, day_str;
        string hour_str, min_str, sec_str;

        ostringstream convert;
        convert << year; year_str = convert.str();
        convert.str(""); convert.clear();
        convert << month; month_str = convert.str();
        convert.str(""); convert.clear();
        convert << day; day_str = convert.str();
        convert.str(""); convert.clear();
        convert << hour; hour_str = convert.str();
        convert.str(""); convert.clear();
        convert << min; min_str = convert.str();
        convert.str(""); convert.clear();
        convert << sec; sec_str = convert.str();
        convert.str(""); convert.clear();

        string date_str = day_str + "_" + month_str + "_" + year_str;
        cout << "DATE STRING   " << date_str << endl;
        string channel_dir = "Craneens" + channelpostfix;
        string date_dir = channel_dir + "/FakeStudies" + date_str + "/";
        int mkdirstatus = mkdir(channel_dir.c_str(), 0777);
        mkdirstatus = mkdir(date_dir.c_str(), 0777);

        string Ntupname = "Craneens" + channelpostfix + "/FakeStudies" + date_str + "/" + dataSetName + postfix + ".root";
        string Ntuptitle = "Craneen_" + channelpostfix;

        TFile* tupfile = new TFile(Ntupname.c_str(), "RECREATE");
        TNtuple* tup = new TNtuple(Ntuptitle.c_str(), Ntuptitle.c_str(),
            "Iso1:Iso2:Pt1:Pt2:MET:nJets:nMtags:HT:SameCharge:nLep");

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
 
        //////////////////////////////////////////////////
        // Loop on events
        //////////////////////////////////////////////////

        cout << "First try to read into dataset::potential tech. bugz::" << endl;
        long long event_end = datasets[d]->NofEvtsToRunOver();
        cout << "Number of total events in dataset = " << event_end << endl;

        int previousRun = -1;
        float BDTScore, bjetpt, SumJetMassX, H, HX, HTHi, HTRat, HT, HTX, HTH, sumpx_X, sumpy_X, sumpz_X, sume_X, jetpt, dRLep, dRbb;
        int nInitJets = 0;

        if(debug) event_end = 10;
        cout << "Looping over events ..." << endl;
        cout << "Will run over " << event_end << " events..." << endl;

        if(event_end < 0) {
            cout << "Starting event larger than number of events.  Exiting." << endl;
            return 1;
        }

        TRootRun* runInfos = new TRootRun();
        datasets[d]->runTree()->SetBranchStatus("runInfos*", 1);
        datasets[d]->runTree()->SetBranchAddress("runInfos", &runInfos);
        //TopologyWorker* topologyW = new TopologyWorker(false);

        //////////////////////////////////////
        // Begin Event Loop
        //////////////////////////////////////

        for(long long ievt = 0; ievt < event_end; ievt++) {
            // define object containers
            vector<TRootElectron *> selectedElectrons, selectedOrigElectrons, selectedVetoElectrons, selectedOrigVetoElectrons;
            vector<TRootMuon *> selectedMuons, looseMuons;;
            vector<TRootPFJet *> selectedJets, selectedUncleanedJets, selectedCleanedJets, MVASelJets1;
            vector<TRootSubstructureJet*> selectedFatJets;
            //selectedElectrons.reserve(10);
            //selectedMuons.reserve(10);

            BDTScore = -99999.0, bjetpt = 0., SumJetMassX = 0., H = 0., HX = 0., HTHi = 0., HTRat = 0;
            HT = 0., HTX = 0., HTH = 0., sumpx_X = 0., sumpy_X = 0., sumpz_X = 0., sume_X = 0., jetpt = 0., dRLep = 0, dRbb = 0;
            nInitJets = 0;

            if(debug) cout << "Event loop: " << ievt << endl;
            if(ievt % 10000 == 0) {
                cout << "Processing the " << ievt << "th event, time = " << ((double)clock() - start) / CLOCKS_PER_SEC
                     << " (" << 100 * ievt / event_end << "%)" << flush << "\r" << endl;
            }
    
            vertex.clear();init_muons.clear();init_electrons.clear();init_jets.clear();init_fatjets.clear();mets.clear();
            event = treeLoader.LoadEvent(ievt, vertex, init_muons, init_electrons, init_jets, init_fatjets, mets, debug);

            float nvertices = vertex.size();
            datasets[d]->eventTree()->LoadTree(ievt);
            string currentFilename = datasets[d]->eventTree()->GetFile()->GetName();
            if(previousFilename != currentFilename) {
                previousFilename = currentFilename;
                iFile++;
                cout << "File changed!!! => " << currentFilename << endl;
            }
            int rBytes = datasets[d]->runTree()->GetEntry(iFile);
            long int currentRun = event->runId();
            long int currentEvent = event->eventId();
            long int LumiBlock = event->lumiBlockId();

            if(isData && Muon)
            {
                if(!event->getHBHENoiseFilter() 
                    || !event->getHBHENoiseIsoFilter() 
                    || !event->getEEBadScFilter() 
                    || !event->getglobalTightHalo2016Filter()
                    || !event->getEcalDeadCellTriggerPrimitiveFilter() 
                    || !event->getPVFilter() 
                    || !event->getBadChCandFilter() 
                    || !event->getBadPFMuonFilter())
                continue;
            }

            eventCount++;

            float rho = event->fixedGridRhoFastjetAll();


            ///////////////////////////////////////////
            //  Trigger
            ///////////////////////////////////////////

            bool trigged = false;
            bool trigged_mumu = false;
            bool trigged_muel = false;
            bool trigged_elel = false;
            bool trigged_mu = false;
            bool trigged_el = false;

            if(Muon && !Electron){
                trigger_mumu->checkAvail(currentRun, datasets, d, &treeLoader, event, verbose);
                trigged_mumu = trigger_mumu->checkIfFired();
                trigger_mu->checkAvail(currentRun, datasets, d, &treeLoader, event, verbose);
                trigged_mu = trigger_mu->checkIfFired();
            } else if(Muon && Electron){
                trigger_muel->checkAvail(currentRun, datasets, d, &treeLoader, event, verbose);
                trigged_muel = trigger_muel->checkIfFired();
                trigger_mu->checkAvail(currentRun, datasets, d, &treeLoader, event, verbose);
                trigged_mu = trigger_mu->checkIfFired();
                trigger_el->checkAvail(currentRun, datasets, d, &treeLoader, event, verbose);
                trigged_el = trigger_el->checkIfFired();
            } else if(!Muon && Electron){
                trigger_elel->checkAvail(currentRun, datasets, d, &treeLoader, event, verbose);
                trigged_elel = trigger_elel->checkIfFired();
                trigger_el->checkAvail(currentRun, datasets, d, &treeLoader, event, verbose);
                trigged_el = trigger_el->checkIfFired();
            }

            bool mmdataset = dName.find("DoubleM")!=string::npos;
            bool medataset = dName.find("MuonEG")!=string::npos;
            bool eedataset = dName.find("DoubleE")!=string::npos;
            bool mdataset = dName.find("SingleM")!=string::npos;
            bool edataset = dName.find("SingleE")!=string::npos;

            bool MM = trigged_mumu;
            bool ME = trigged_muel;
            bool EE = trigged_elel;
            bool M = trigged_mu;
            bool E = trigged_el;


            if(isData){
                if(Muon && !Electron){
                    if(mmdataset) trigged = MM;
                    else if(mdataset) trigged = M;// && !MM;
                    else {cerr << "Trigger Error" << endl; exit(1);}
                }
                else if(Muon && Electron){
                    if(medataset) trigged = ME;
                    else if(mdataset) trigged = M && !ME;
                    else if(edataset) trigged = E && !ME && !M;
                    else {cerr << "Trigger Error" << endl; exit(1);}
                }
                else if(!Muon && Electron){
                    if(eedataset) trigged = EE;
                    else if(edataset) trigged = E && !EE;
                    else {cerr << "Trigger Error" << endl; exit(1);}
                }
                else {cerr << "Error" << endl; exit(1);}
            } else {
                cerr << "Trigger Error Not Data" << endl; exit(1);
            }
 
            if(debug) cout << "triggered? Y/N?  " << trigged << endl;
 

            //////////////////////////////////////
            ///  Jet Energy Scale Corrections  ///
            //////////////////////////////////////
            
            if(applyJEC) jetTools->correctJets(init_jets, event->fixedGridRhoFastjetAll(), isData);


            /////////////////////////////////////
            // Init Jet Plots for ISR reweight //
            /////////////////////////////////////

            for(int iJet = 0; iJet < init_jets.size(); iJet++) {
                if(init_jets[iJet]->genParticleIndex() == -1) {
                    nInitJets++;
                }
            }


            //////////////////////////////////
            //      Event selection         //
            //////////////////////////////////

            
            // Declare selection instance
            Run2Selection selection(init_jets, init_fatjets, init_muons, init_electrons, mets, rho);
            selectedMuons.clear(); selectedElectrons.clear(); selectedOrigElectrons.clear(); selectedVetoElectrons.clear(); selectedOrigVetoElectrons.clear();
            looseMuons.clear();
            // Define object selection cuts
            if(Muon && Electron && dilepton) {
                selectedMuons = selection.GetSelectedMuons(20., 2.4, 0.40, "Loose", "Summer16");
                selectedOrigElectrons = selection.GetSelectedElectrons(20., 2.4, "Loose", "Spring16_80X", true, true);
                selectedOrigVetoElectrons = selection.GetSelectedElectrons(15., 2.4, "Veto", "Spring16_80X", true, true);
            } if(Muon && !Electron && dilepton) {
                selectedMuons = selection.GetSelectedMuons(0., 2.4, 0, "Fake", "Summer16");
                looseMuons =  selection.GetSelectedMuons(20., 2.4, 0.40, "Loose", "Summer16");
                selectedOrigElectrons = selection.GetSelectedElectrons(20., 2.4, "Loose", "Spring16_80X", true, true);
                selectedOrigVetoElectrons = selection.GetSelectedElectrons(15., 2.4, "Veto", "Spring16_80X", true, true);
            } if(!Muon && Electron && dilepton) {
                selectedMuons = selection.GetSelectedMuons(20., 2.4, 0.40, "Loose", "Summer16");
                selectedOrigElectrons = selection.GetSelectedElectrons(20., 2.4, "Loose", "Spring16_80X", true, true);
                selectedOrigVetoElectrons = selection.GetSelectedElectrons(15., 2.4, "Veto", "Spring16_80X", true, true);
            }

            for(int e_iter=0; e_iter<selectedOrigElectrons.size();e_iter++){
                if(selectedOrigElectrons[e_iter]->Eta()<=1.4442 || selectedOrigElectrons[e_iter]->Eta()>=1.5660){
                    selectedElectrons.push_back(selectedOrigElectrons[e_iter]);
                }
            }
            for(int e_iter=0; e_iter<selectedOrigVetoElectrons.size();e_iter++){
                if(selectedOrigVetoElectrons[e_iter]->Eta()<=1.4442 || selectedOrigVetoElectrons[e_iter]->Eta()>=1.5660){
                    selectedVetoElectrons.push_back(selectedOrigVetoElectrons[e_iter]);
                }
            }

            if(Muon && !Electron && dilepton && selectedMuons.size() < 1) continue;
            if(Muon && !Electron && dilepton && looseMuons.size() > 0 && looseMuons[0]->Pt() < 25.0) continue;
            
            if(!Muon && Electron && dilepton && selectedElectrons.size() == 0) continue;
            if(!Muon && Electron && dilepton && selectedElectrons[0]->Pt() < 25.0) continue;
            
            if(Muon && Electron && dilepton){
                if(selectedMuons.size() == 0 && selectedElectrons.size() == 0) continue;
                if(selectedMuons.size() > 0 && selectedElectrons.size() == 0 && selectedMuons[0]->Pt() < 25.0) continue;
                if(selectedMuons.size() == 0 && selectedElectrons.size() > 0 && selectedElectrons[0]->Pt() < 25.0) continue;
                if(selectedMuons.size() > 0 && selectedElectrons.size() > 0 && selectedMuons[0]->Pt() < 25.0 && selectedElectrons[0]->Pt() < 25.0) continue;
            }

            selectedUncleanedJets.clear(); selectedFatJets.clear(); selectedCleanedJets.clear(); selectedJets.clear();
            selectedUncleanedJets = selection.GetSelectedJets(25., 2.4, true, "Loose");

            for(int unj = 0; unj < selectedUncleanedJets.size(); unj++) {
                bool isClose = false;
                for(int e = 0; e < selectedElectrons.size(); e++) {
                    if(selectedElectrons[e]->DeltaR(*selectedUncleanedJets[unj]) < 0.3)
                        isClose = true;
                }
                for(int mu = 0; mu < looseMuons.size(); mu++) {
                    if(looseMuons[mu]->DeltaR(*selectedUncleanedJets[unj]) < 0.3)
                        isClose = true;
                }
                if(!isClose)
                    selectedCleanedJets.push_back(selectedUncleanedJets[unj]);
            }

            for(int cj = 0; cj < selectedCleanedJets.size(); cj++) {
                if(selectedCleanedJets[cj]->btag_combinedInclusiveSecondaryVertexV2BJetTags() > 0.8484) 
                    selectedJets.push_back(selectedCleanedJets[cj]);
                else if(selectedCleanedJets[cj]->Pt() > 30)
                    selectedJets.push_back(selectedCleanedJets[cj]);
            }
            sort(selectedJets.begin(), selectedJets.end(), HighestPt());

            vector<TRootPFJet*> selectedLBJets;
            vector<TRootPFJet*> selectedMBJets;
            vector<TRootPFJet*> selectedTBJets;

            int nMu = 0, nEl = 0, nEv = 0, nLep = 0;
            nEv = selectedVetoElectrons.size();
            nMu = selectedMuons.size();
            nEl = selectedElectrons.size();

            vector<TLorentzVector> selectedMuonsTLV_JC, selectedElectronsTLV_JC, selectedJetsTLV;
            vector<TRootMCParticle*> mcParticlesMatching_;

            ////////////////////////////////////
            // Preselection Lepton Operations //
            ////////////////////////////////////

            float diLepMass = 0;
            bool ZVeto = false, sameCharge = false;
            float ZMass = 91, ZMassWindow = 15;
            int cj1 = 0, cj2 = 0, lidx1 = 0, lidx2 = 0;
            TLorentzVector lep1, lep2, diLep;
            vector<pair<float, pair<TRootLepton*, TRootLepton*> > > LeptonPairs;

            for(int selmu = 0; selmu < selectedMuons.size(); selmu++) {
                selectedMuonsTLV_JC.push_back(*selectedMuons[selmu]);
            }
            for(int selel = 0; selel < selectedElectrons.size(); selel++) {
                selectedElectronsTLV_JC.push_back(*selectedElectrons[selel]);
            }
            for(Int_t seljet = 0; seljet < selectedJets.size(); seljet++) {
                selectedJetsTLV.push_back(*selectedJets[seljet]);
            }

            if(nMu >= 2 && nEl == 0 && Muon && !Electron) // Di-Muon Selection
            {
                lep1 = selectedMuonsTLV_JC[0];
                lep2 = selectedMuonsTLV_JC[1];
                if(selectedMuons[0]->charge() == selectedMuons[1]->charge())
                    sameCharge = true;
                nLep = nMu;
            } else if(nEl >= 2 && nMu == 0 && Electron && !Muon) // Di-Electron Selection criteria
            {
                lep1 = selectedElectronsTLV_JC[0];
                lep2 = selectedElectronsTLV_JC[1];
                if(selectedElectrons[0]->charge() == selectedElectrons[1]->charge())
                    sameCharge = true;
                nLep = nEl;
            } else if(nEl >= 1 && nMu >= 1 && Electron && Muon) // Muon-Electron Selection
            {
                lep1 = selectedMuonsTLV_JC[0];
                lep2 = selectedElectronsTLV_JC[0];
                if(selectedMuons[0]->charge() == selectedElectrons[0]->charge())
                    sameCharge = true;
                nLep = nMu + nEl;
            }

            if(!sameCharge && nLep==2) {
                diLep = lep1 + lep2;
                diLepMass = diLep.M();
                for(Int_t seljet = 0; seljet < selectedJetsTLV.size(); seljet++) {
                    if(lep1.DeltaR(selectedJetsTLV[seljet]) < lep1.DeltaR(selectedJetsTLV[cj1]))
                        cj1 = seljet;
                    if(lep2.DeltaR(selectedJetsTLV[seljet]) < lep2.DeltaR(selectedJetsTLV[cj2]))
                        cj2 = seljet;
                }
                if(selectedJetsTLV.size() > 0) {
                    if(lep1.DeltaPhi(selectedJetsTLV[cj1]) < 0.05) {
                        float HOverE = (selectedJets[cj1]->chargedHadronEnergyFraction() + selectedJets[cj1]->neutralHadronEnergyFraction()) /
                                       (selectedJets[cj1]->chargedEmEnergyFraction() + selectedJets[cj1]->neutralEmEnergyFraction());
                    }
                    if(lep2.DeltaPhi(selectedJetsTLV[cj2]) < 0.05) {
                        float HOverE = (selectedJets[cj2]->chargedHadronEnergyFraction() +selectedJets[cj2]->neutralHadronEnergyFraction()) /
                                       (selectedJets[cj2]->chargedEmEnergyFraction() + selectedJets[cj2]->neutralEmEnergyFraction());
                    }
                }
            }

            float temp_HT = 0., HTb = 0.;

            for(Int_t seljet = 0; seljet < selectedJets.size(); seljet++) {
                temp_HT += selectedJets[seljet]->Pt();
                if(selectedJets[seljet]->btag_combinedInclusiveSecondaryVertexV2BJetTags() > 0.5426) {
                    selectedLBJets.push_back(selectedJets[seljet]);
                    if(selectedJets[seljet]->btag_combinedInclusiveSecondaryVertexV2BJetTags() > 0.8484) {
                        selectedMBJets.push_back(selectedJets[seljet]);
                        if(selectedJets[seljet]->btag_combinedInclusiveSecondaryVertexV2BJetTags() > 0.9535) {
                            selectedTBJets.push_back(selectedJets[seljet]);
                        }
                    }
                }
            }

            
            float nJets = selectedJets.size();
            float nMtags = selectedMBJets.size();
            float nLtags = selectedLBJets.size();
            float nTtags = selectedTBJets.size();
            float nFatJets = selectedFatJets.size();

            bool isGoodPV = selection.isPVSelected(vertex, 4, 24., 2);
            if(debug) cout << "PrimaryVertexBit: " << isGoodPV << " TriggerBit: " << trigged << endl;


            /////////////////////////////////
            // Applying baseline selection //
            /////////////////////////////////

            if(!trigged) continue;
            trigCount++;

            if(!isGoodPV) continue;

            if(debug)
                cout << " applying baseline event selection... nMu = " << nMu << " nEl = " << nEl << " ZVeto: " << ZVeto << " sameCharge: " << sameCharge << endl;

            if(Muon && Electron && dilepton) {
                if(!(nMu == 1 && nEl == 1 && nEv == 1 && !sameCharge))
                    continue;
            } else if(Muon && !Electron && dilepton) {
                if(!(nMu >= 2 && nEl == 0 && !ZVeto))// && !sameCharge))
                    continue;
            } else if(!Muon && Electron && dilepton) {
                if(!(nMu == 0 && nEl == 2 && nEv == 2 && !ZVeto && !sameCharge))
                    continue;
            } else {
                cerr << "Correct Channel not selected." << endl;
                exit(1);
            }

            if(debug)
                cout << "HT: " << temp_HT << " nJets: " << nJets << " nMTags: " << nMtags << endl;
            vector<TLorentzVector*> selectedLeptonTLV_JC;

            passed++;
/*

            //////////////////////
            //   W/Top tagging  //
            //////////////////////

            float nTopTags = 0;
            float nWTags = 0;
            for(int fatjet = 0; fatjet < nFatJets; fatjet++) {
                float tau1 = selectedFatJets[fatjet]->Tau1();
                float tau2 = selectedFatJets[fatjet]->Tau2();
                float prunedmass = selectedFatJets[fatjet]->PrunedMass();
                float nsubjets = selectedFatJets[fatjet]->CmsTopTagNsubjets();
                float minmass = selectedFatJets[fatjet]->CmsTopTagMinMass();
                float topmass = selectedFatJets[fatjet]->CmsTopTagMass();
                // W-tagging
                if((tau2 / tau1) > 0.6 && prunedmass > 50.0) {
                    nWTags++;                    // cout <<"W-TAG!"<<endl;
                }
                // Top-tagging
                if(nsubjets > 2 && minmass > 50.0 && topmass > 150.0) {
                    nTopTags++;                    // cout <<"TOP-TAG!"<<endl;
                }
            }


            sort(selectedJets.begin(), selectedJets.end(), HighestCVSBtag());


            //////////////////////////////////////
            // MVA Hadronic Top Reconstructions //
            //////////////////////////////////////

            float TriJetMass, DiJetMass;
            TLorentzVector Wh, Bh, Th;
            int wj1;
            int wj2;
            int bj1;

            TLorentzVector sumjet_X, sumjet_b;
            float sumpx_X = 0, sumpy_X = 0, sumpz_X = 0, sume_X =0, SumJetMassX = 0;
            if(nJets >= 40 && nMtags >= 2) {
                jetCombiner->ProcessEvent_SingleHadTop(datasets[d], mcParticlesMatching_, selectedJets, selectedLeptonTLV_JC[0], 1);
                if(!TrainMVA) {
                    MVAvals1 = jetCombiner->getMVAValue(MVAmethod, 1); // 1 means the highest MVA value
                    topness = MVAvals1.first;
                    for(Int_t seljet1 = 0; seljet1 < selectedJets.size(); seljet1++) {
                        if(seljet1 == MVAvals1.second[0] || seljet1 == MVAvals1.second[1] || seljet1 == MVAvals1.second[2]) {
                            MVASelJets1.push_back(selectedJets[seljet1]);
                            continue;
                        }
                        sumpx_X = sumpx_X + selectedJets[seljet1]->Px();
                        sumpy_X = sumpy_X + selectedJets[seljet1]->Py();
                        sumpz_X = sumpz_X + selectedJets[seljet1]->Pz();
                        sume_X = sume_X + selectedJets[seljet1]->E();
                    }
                    sumjet_X = TLorentzVector (sumpx_X, sumpy_X, sumpz_X,sume_X );
                    SumJetMassX = sumjet_X.M();

                    // check data-mc agreement of kin. reco. variables.
                    float mindeltaR = 100.;
                    float mindeltaR_temp = 100.;
                    // define the jets from W as the jet pair with smallest deltaR
                    for(int m = 0; m < MVASelJets1.size(); m++) {
                        for(int n = 0; n < MVASelJets1.size(); n++) {
                            if(n == m) continue;
                            TLorentzVector lj1 = *MVASelJets1[m];
                            TLorentzVector lj2 = *MVASelJets1[n];
                            mindeltaR_temp = lj1.DeltaR(lj2);
                            if(mindeltaR_temp < mindeltaR) {
                                mindeltaR = mindeltaR_temp;
                                wj1 = m;
                                wj2 = n;
                            }
                        }
                    }
                    // find the index of the jet not chosen as a W-jet
                    for(unsigned int p = 0; p < MVASelJets1.size(); p++) {
                        if(p != wj1 && p != wj2)
                            bj1 = p;
                    }

                    if(debug)
                        cout << "Processing event with jetcombiner : 3 " << endl;

                    // now that putative b and W jets are chosen, calculate the six kin. variables.
                    Wh = *MVASelJets1[wj1] + *MVASelJets1[wj2];
                    Bh = *MVASelJets1[bj1];
                    Th = Wh + Bh;

                    TriJetMass = Th.M();

                    DiJetMass = Wh.M();
                    // DeltaR
                    float AngleThWh = fabs(Th.DeltaPhi(Wh));
                    float AngleThBh = fabs(Th.DeltaPhi(Bh));

                    float btag = MVASelJets1[bj1]->btag_combinedInclusiveSecondaryVertexV2BJetTags();

                    double PtRat = ((*MVASelJets1[0] + *MVASelJets1[1] + *MVASelJets1[2]).Pt()) / (MVASelJets1[0]->Pt() + MVASelJets1[1]->Pt() + MVASelJets1[2]->Pt());
                    double diLepThdR = fabs(Th.DeltaR(diLep));
                    double diLepThdPhi = fabs(Th.DeltaPhi(diLep));

                    if(debug)
                        cout << "Processing event with jetcombiner : 4 " << endl;

                    if(debug)
                        cout << "Processing event with jetcombiner : 8 " << endl;
                }
            }

            if(nEl > 0) {
                float epRat = selectedElectrons[0]->E() / selectedElectrons[0]->P();
            }

            dRLep = lep1.DeltaR(lep2);

            HT = 0;
            float HT1M2L = 0, H1M2L = 0, HTbjets = 0, HT2M = 0, H2M = 0, dRbb = 0;

            for(Int_t seljet1 = 0; seljet1 < selectedJets.size(); seljet1++) {
                if(nMtags >= 2 && seljet1 >= 2) {
                    jetpt = selectedJets[seljet1]->Pt();
                    HT2M = HT2M + jetpt;
                    H2M = H2M + selectedJets[seljet1]->P();
                }
                if(selectedJets[seljet1]->btag_combinedInclusiveSecondaryVertexV2BJetTags() > 0.8484) {
                    HTb += selectedJets[seljet1]->Pt();
                }
                // Event-level variables
                jetpt = selectedJets[seljet1]->Pt();
                HT = HT + jetpt;
                H = H + selectedJets[seljet1]->P();
            }
            if(nJets>1) dRbb = fabs(selectedJets[0]->DeltaR(*selectedJets[1]));
            if(nJets>1) HTRat = (selectedJets[0]->Pt() + selectedJets[1]->Pt()) / HT;
            if(nJets>1) HTH = HT / H;

            sort(selectedJets.begin(), selectedJets.end(), HighestPt()); // order Jets wrt Pt for tuple output
*/
            float reliso1, reliso2;
            if(dilepton && Muon && Electron) {
                reliso1 = selectedMuons[0]->relPfIso(4,0.5);
                reliso2 = ElectronRelIso(selectedElectrons[0],rho);

            }
            if(dilepton && Muon && !Electron) {
                reliso1 = selectedMuons[0]->relPfIso(4,0.5);
                reliso2 = selectedMuons[1]->relPfIso(4,0.5);
            }
            if(dilepton && !Muon && Electron) {
                reliso1 = ElectronRelIso(selectedElectrons[0],rho);
                reliso2 = ElectronRelIso(selectedElectrons[1],rho);
            }

            if(nMtags >= 1) {
                bjetpt = selectedMBJets[0]->Pt();
            }

            ////////////////////
            // Topology Plots //
            ////////////////////
/*            float tSph = 0, dSph = 0, tdSph = 0, tCen = 0, dCen = 0, tdCen = 0;

            topologyW->setPartList(selectedJetsTLV, selectedJetsTLV);
            float fSphericity = topologyW->get_sphericity();
            float fOblateness = topologyW->oblateness();
            float fAplanarity = topologyW->get_aplanarity();
            float fh10 = topologyW->get_h10();
            float fh20 = topologyW->get_h20();
            float fh30 = topologyW->get_h30();
            float fh40 = topologyW->get_h40();
            float fh50 = topologyW->get_h50();
            float fh60 = topologyW->get_h60();
            float fht = topologyW->get_ht();
            float fht3 = topologyW->get_ht3();
            float fet0 = topologyW->get_et0();
            float fsqrts = topologyW->get_sqrts();
            float fnjetW = topologyW->get_njetW();
            float fet56 = topologyW->get_et56();
            float fcentrality = topologyW->get_centrality();

            vector<TLorentzVector> selectedParticlesTLV, diLepSystemTLV, topDiLepSystemTLV;
            // collection Total Event TLVs
            selectedParticlesTLV.insert(selectedParticlesTLV.end(), selectedElectronsTLV_JC.begin(), selectedElectronsTLV_JC.end());
            selectedParticlesTLV.insert(selectedParticlesTLV.end(), selectedMuonsTLV_JC.begin(), selectedMuonsTLV_JC.end());
            selectedParticlesTLV.insert(selectedParticlesTLV.end(), selectedJetsTLV.begin(), selectedJetsTLV.end());
            selectedParticlesTLV.push_back(*mets[0]);
            // collecting diLep TLVs
            diLepSystemTLV.push_back(lep1);
            diLepSystemTLV.push_back(lep2);
            diLepSystemTLV.push_back(*mets[0]);
            // collecting topDiLep TLVs
            topDiLepSystemTLV.insert(topDiLepSystemTLV.end(), diLepSystemTLV.begin(), diLepSystemTLV.end());
            if(!TrainMVA) {
                if(nJets >= 4) {
                    topDiLepSystemTLV.push_back(*MVASelJets1[wj1]);
                    topDiLepSystemTLV.push_back(*MVASelJets1[wj2]);
                    topDiLepSystemTLV.push_back(*MVASelJets1[bj1]);
                }
                tSph = Sphericity(selectedParticlesTLV), tCen = Centrality(selectedParticlesTLV);
                dSph = Sphericity(diLepSystemTLV), dCen = Centrality(diLepSystemTLV);
                tdSph = Sphericity(topDiLepSystemTLV), tdCen = Centrality(topDiLepSystemTLV);
            }
 */

            ////////////////////
            // Filling nTuple //
            //////////////////// 
 
            float vals[11] = {reliso1, reliso2, 0, 0, mets[0]->Pt(), nJets, nMtags, temp_HT, sameCharge, nLep};


            if(Muon && Electron) {
                vals[2] = selectedMuons[0]->Pt();
                vals[3] = selectedElectrons[0]->Pt();
            }
            if(Muon && !Electron) {
                vals[2] = selectedMuons[0]->Pt();
                vals[3] = selectedMuons[1]->Pt();
            }
            if(!Muon && Electron) {
                vals[2] = selectedElectrons[0]->Pt();
                vals[3] = selectedElectrons[1]->Pt();
            }
            

            tup->Fill(vals);

/*            
            if(Muon && Electron) {
                TLVlep1->SetPxPyPzE(selectedMuons[0]->Px(), selectedMuons[0]->Py(), selectedMuons[0]->Pz(), selectedMuons[0]->E());
                TLVlep2->SetPxPyPzE(selectedElectrons[0]->Px(), selectedElectrons[0]->Py(), selectedElectrons[0]->Pz(), selectedElectrons[0]->E());
            } 
            if(Muon && !Electron) {
                TLVlep1->SetPxPyPzE(selectedMuons[0]->Px(), selectedMuons[0]->Py(), selectedMuons[0]->Pz(), selectedMuons[0]->E());
                TLVlep2->SetPxPyPzE(selectedMuons[1]->Px(), selectedMuons[1]->Py(), selectedMuons[1]->Pz(), selectedMuons[1]->E());
            }
            if(!Muon && Electron) {
                TLVlep1->SetPxPyPzE(selectedElectrons[0]->Px(), selectedElectrons[0]->Py(), selectedElectrons[0]->Pz(), selectedElectrons[0]->E());
                TLVlep2->SetPxPyPzE(selectedElectrons[1]->Px(), selectedElectrons[1]->Py(), selectedElectrons[1]->Pz(), selectedElectrons[1]->E());
            }

            sort(selectedJets.begin(), selectedJets.end(), HighestCVSBtag());

            TLVjet1->SetPxPyPzE(selectedJets[0]->Px(), selectedJets[0]->Py(), selectedJets[0]->Pz(), selectedJets[0]->E());
            TLVjet2->SetPxPyPzE(selectedJets[1]->Px(), selectedJets[1]->Py(), selectedJets[1]->Pz(), selectedJets[1]->E());
            TLVjet3->SetPxPyPzE(selectedJets[2]->Px(), selectedJets[2]->Py(), selectedJets[2]->Pz(), selectedJets[2]->E());
            TLVjet4->SetPxPyPzE(selectedJets[3]->Px(), selectedJets[3]->Py(), selectedJets[3]->Pz(), selectedJets[3]->E());
            EventID[0]=event->lumiBlockId();
            EventID[1]=event->lumiBlockId();
            EventID[2]=event->eventId();
            tree->Fill();
*/


        } // End Loop on Events

        tupfile->cd();
        tup->Write();
//        tree->Write();
        tupfile->Close();


        cout << "n events passing selection  = " << passed << endl;
        cout << "n events passing trigger    = " << trigCount << endl;
        cout << "n events passing filter     = " << eventCount << endl;
        cout << "trigger eff. = " << (float) trigCount/(float) eventCount << endl;

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

float ElectronRelIso(TRootElectron* el, float rho)
{
    double EffectiveArea = 0.;
    // Updated to Spring 2015 EA from
    // https://github.com/cms-sw/cmssw/blob/CMSSW_7_4_14/RecoEgamma/ElectronIdentification/data/Spring15/effAreaElectrons_cone03_pfNeuHadronsAndPhotons_25ns.txt#L8
    if(fabs(el->superClusterEta()) >= 0.0 && fabs(el->superClusterEta()) < 1.0)
        EffectiveArea = 0.1752;
    if(fabs(el->superClusterEta()) >= 1.0 && fabs(el->superClusterEta()) < 1.479)
        EffectiveArea = 0.1862;
    if(fabs(el->superClusterEta()) >= 1.479 && fabs(el->superClusterEta()) < 2.0)
        EffectiveArea = 0.1411;
    if(fabs(el->superClusterEta()) >= 2.0 && fabs(el->superClusterEta()) < 2.2)
        EffectiveArea = 0.1534;
    if(fabs(el->superClusterEta()) >= 2.2 && fabs(el->superClusterEta()) < 2.3)
        EffectiveArea = 0.1903;
    if(fabs(el->superClusterEta()) >= 2.3 && fabs(el->superClusterEta()) < 2.4)
        EffectiveArea = 0.2243;
    if(fabs(el->superClusterEta()) >= 2.4 && fabs(el->superClusterEta()) < 5.0)
        EffectiveArea = 0.2687;

    double isoCorr = 0;
    isoCorr = el->neutralHadronIso(3) + el->photonIso(3) - rho * EffectiveArea;
    float isolation = (el->chargedHadronIso(3) + (isoCorr > 0.0 ? isoCorr : 0.0)) / (el->Pt());

    return isolation;
}

float MuonRelIso(TRootMuon* mu)
{
    float isolation = (mu->chargedHadronIso(4) + max( 0.0, mu->neutralHadronIso(4) + mu->photonIso(4) - 0.5*mu->puChargedHadronIso(4) ) ) / (mu->Pt()); // dBeta corrected
    return isolation;
}

