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
    
    cout << "*************************************************************" << endl;
    cout << " Beginning of the program for the FourTop search ! " << endl;
    cout << "*************************************************************" << endl;


    ///////////////////////////////////////
    //      Configuration                //
    ///////////////////////////////////////

    string channelpostfix = "";
    float Luminosity; // pb^-1 

    bool debug = false;
    bool dilepton = true;
    bool Muon = false;
    bool Electron = false;
    bool bTagCSVReweight = true;
    bool bLeptonSF = true;
    bool applyJER = true;
    bool applyJEC = true;
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

    /////////////////////////////
    //   Initialize Trigger    //
    /////////////////////////////

    Trigger* trigger_mumu = new Trigger(1, 0, 0, 1,0,0,0);  // mu , el, single, double, tri, met, jet
    Trigger* trigger_muel = new Trigger(1, 1, 0, 1,0,0,0);
    Trigger* trigger_elel = new Trigger(0, 1, 0, 1,0,0,0);
    Trigger* trigger_mu = new Trigger(1, 0, 1, 0,0,0,0);
    Trigger* trigger_el = new Trigger(0, 1, 1, 0,0,0,0);

    ////////////////////////////////
    // Setting Up Scaling Objects //
    ////////////////////////////////

    //////////////////////////////////////////////////////
    //     bTag calibration reader and weight tools     //
    //////////////////////////////////////////////////////
    cout << "Loading btag calibration files ..." << endl;
    BTagCalibrationReader * reader_csvv2; //for csv reshaping 

    if(bTagCSVReweight && !isData){
        BTagCalibration calib_csvv2("csvv2", "../TopTreeAnalysisBase/Calibrations/BTagging/CSVv2Moriond17_2017_1_26_BtoH.csv");
        reader_csvv2 = new BTagCalibrationReader(&calib_csvv2, BTagEntry::OP_RESHAPING, "iterativefit", "central");
    }

    /////////////////////////////////////////////////
    //                   Lepton SF                 //
    /////////////////////////////////////////////////
    cout << "Loading leptonsf files ..." << endl;
    MuonSFWeight* muonSFWeightID_GH;
    MuonSFWeight* muonSFWeightID_BCDEF;
    MuonSFWeight* muonSFWeightIso_GH;
    MuonSFWeight* muonSFWeightIso_BCDEF;
    //MuonSFWeight* muonSFWeightTrig_BCDEF;
    //MuonSFWeight* muonSFWeightTrig_GH;

    TFile *muontrackfile = new TFile("../TopTreeAnalysisBase/Calibrations/LeptonSF/MuonSF/Tracking_EfficienciesAndSF_BCDEFGH.root","read");
    TGraph* h_muonSFWeightTrack = static_cast<TGraph*>( muontrackfile->Get("ratio_eff_eta3_dr030e030_corr")->Clone() );//Tracking efficiency as function of eta

    ElectronSFWeight* electronSFWeight;
    ElectronSFWeight* electronSFWeightReco;
    if(bLeptonSF) {
        if(Muon) {
            muonSFWeightID_GH = new MuonSFWeight("../TopTreeAnalysisBase/Calibrations/LeptonSF/MuonSF/20170413/IDEfficienciesAndSF_GH.root",
                                              "MC_NUM_LooseID_DEN_genTracks_PAR_pt_eta/abseta_pt_ratio", true, false, false);
            muonSFWeightIso_GH = new MuonSFWeight("../TopTreeAnalysisBase/Calibrations/LeptonSF/MuonSF/20170413/IsoEfficienciesAndSF_GH.root",
                                              "LooseISO_LooseID_pt_eta/abseta_pt_ratio", true, false, false);
            muonSFWeightID_BCDEF = new MuonSFWeight("../TopTreeAnalysisBase/Calibrations/LeptonSF/MuonSF/20170413/IDEfficienciesAndSF_BCDEF.root",
                                              "MC_NUM_LooseID_DEN_genTracks_PAR_pt_eta/abseta_pt_ratio", true, false, false);
            muonSFWeightIso_BCDEF = new MuonSFWeight("../TopTreeAnalysisBase/Calibrations/LeptonSF/MuonSF/20170413/IsoEfficienciesAndSF_BCDEF.root",
                                              "LooseISO_LooseID_pt_eta/abseta_pt_ratio", true, false, false);
            //muonSFWeightTrig_BCDEF = new MuonSFWeight("../TopTreeAnalysisBase/Calibrations/LeptonSF/MuonSF/SingleMuonTrigger_EfficienciesAndSF_RunsBCDEF.root",
            //                                  "IsoMu24_OR_IsoTkMu24_PtEtaBins/abseta_pt_ratio", true, false, false);
            //muonSFWeightTrig_GH = new MuonSFWeight("../TopTreeAnalysisBase/Calibrations/LeptonSF/MuonSF/SingleMuonTrigger_EfficienciesAndSF_RunsGH.root",
            //                                  "IsoMu24_OR_IsoTkMu24_PtEtaBins/abseta_pt_ratio", true, false, false);
        }
        if(Electron) {
            electronSFWeight = new ElectronSFWeight("../TopTreeAnalysisBase/Calibrations/LeptonSF/ElectronSF/20170413/egammaEffi.txt_EGM2D_IDcutbLoose_20170413.root",
                    "EGamma_SF2D", true, false, false);
            electronSFWeightReco = new ElectronSFWeight("../TopTreeAnalysisBase/Calibrations/LeptonSF/ElectronSF/20170413/egammaEffi.txt_EGM2D_reco_20170413.root",
                    "EGamma_SF2D", true, false, false, true);
        }
    }

    /////////////////////////////////////////////////
    //               Pu reweighting                //
    /////////////////////////////////////////////////
    cout << "Loading lumiweights files..." << endl;
    LumiReWeighting LumiWeights;
    LumiReWeighting LumiWeights_up;
    LumiReWeighting LumiWeights_down;

    LumiWeights = LumiReWeighting(
        "../TopTreeAnalysisBase/Calibrations/PileUpReweighting/MCPileup_Summer16.root",
        "../TopTreeAnalysisBase/Calibrations/PileUpReweighting/pileup_2016Data80X_Run271036-284044Cert__Full2016DataSet.root",
        "pileup", "pileup");
    LumiWeights_up = LumiReWeighting(
        "../TopTreeAnalysisBase/Calibrations/PileUpReweighting/MCPileup_Summer16.root",
        "../TopTreeAnalysisBase/Calibrations/PileUpReweighting/pileup_2016Data80X_Run271036-284044Cert__Full2016DataSet_sysPlus.root",
        "pileup", "pileup");
    LumiWeights_down = LumiReWeighting(
        "../TopTreeAnalysisBase/Calibrations/PileUpReweighting/MCPileup_Summer16.root",
        "../TopTreeAnalysisBase/Calibrations/PileUpReweighting/pileup_2016Data80X_Run271036-284044Cert__Full2016DataSet_sysMinus.root",
        "pileup", "pileup");

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
    } else {
        JetCorrectorParameters *L1JetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_MC/Summer16_23Sep2016V4_MC_L1FastJet_AK4PFchs.txt");
        vCorrParam.push_back(*L1JetCorPar);
        JetCorrectorParameters *L2JetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_MC/Summer16_23Sep2016V4_MC_L2Relative_AK4PFchs.txt");
        vCorrParam.push_back(*L2JetCorPar);
        JetCorrectorParameters *L3JetCorPar = new JetCorrectorParameters(pathCalJEC+"/Summer16_23Sep2016V4_MC/Summer16_23Sep2016V4_MC_L3Absolute_AK4PFchs.txt");
        vCorrParam.push_back(*L3JetCorPar);
        
        jecUnc = new JetCorrectionUncertainty(pathCalJEC+"/Summer16_23Sep2016V4_MC/Summer16_23Sep2016V4_MC_Uncertainty_AK4PFchs.txt");
    }


    JetTools* jetTools = new JetTools(vCorrParam, jecUnc, true);

    /////////////////////////////////
    //  Loop over Datasets
    /////////////////////////////////

    //cout << "Find sample with equivalent lumi ..." << theDataset->EquivalentLumi() << endl;
    //cout << "Rescale to an integrated luminosity of ..." << Luminosity << " pb^-1" << endl;


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
        string channel_dir = "Craneens" + channelpostfix;
        string date_dir = channel_dir + "/Craneens" + date_str + "/";
        string cutflow_dir = channel_dir + "/Cutflow" + date_str + "/";
        int mkdirstatus = mkdir(channel_dir.c_str(), 0777);
        mkdirstatus = mkdir(date_dir.c_str(), 0777);
        //mkdirstatus = mkdir(cutflow_dir.c_str(), 0777);

        string Ntupname = "Craneens" + channelpostfix + "/Craneens" + date_str + "/" + dataSetName + postfix + ".root";
        string Ntuptitle = "Craneen_" + channelpostfix;

        TFile* tupfile = new TFile(Ntupname.c_str(), "RECREATE");
        TNtuple* tup = new TNtuple(Ntuptitle.c_str(), Ntuptitle.c_str(), "lep1Pt:lep2Pt:lep1Iso:lep2Iso:nJets:HT:MET:scaleFactor");

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
        long int event_end = datasets[d]->NofEvtsToRunOver();
        cout << "Number of total events in dataset = " << event_end << endl;

        int previousRun = -1;
        int start = 0;

        //event_end = 10; //artifical ending for debug
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
            // define object containers
            vector<TRootElectron *> selectedElectrons, selectedOrigElectrons;
            vector<TRootElectron *> selectedVetoElectrons, selectedOrigVetoElectrons;
            vector<TRootMuon *> selectedMuons, selectedLooseMuons;
            vector<TRootPFJet *> selectedJets, selectedCleanedJets, selectedUncleanedJets;
            vector<TRootSubstructureJet*> selectedFatJets;
            selectedElectrons.reserve(10);
            selectedMuons.reserve(10);

            float lep1Pt, lep2Pt;
            float centralWeight = 1, weight1 = 1, weight2 = 1, weight3 = 1, weight4 = 1,
                  weight5 = 1, weight6 = 1, weight7 = 1, weight8 = 1, weight_hdamp_up = 1, weight_hdamp_dw = 1,
                  ttXrew  = 1., ttXrew_up = 1., ttXrew_down = 1., weight_ct10 = 1., weight_mmht14 = 1.;
            int ttXtype = -1;
            if(debug) cout << "Event loop " << ievt << endl;
            if(ievt % 10000 == 0) {
                cout << "Processing the " << ievt << "th event, time = " << ((double)clock() - start) / CLOCKS_PER_SEC
                     << " (" << 100 * (ievt - start) / (event_end - start) << "%)" << flush << "\r" << endl;
            }

            float scaleFactor = 1., flag_ = 1.; float genHT = 0.; int n_genjets = 0, n_genleps = 0;

            genjets.clear();vertex.clear();init_muons.clear();init_electrons.clear();init_jets.clear();init_fatjets.clear();mets.clear();
            event = treeLoader.LoadEvent(ievt, vertex, init_muons, init_electrons, init_jets, init_fatjets, mets, debug); // load event

            if(!isData && dataSetName.find("TTJets")!=string::npos) {
                genjets = treeLoader.LoadGenJet(ievt, false);
                mcpart = treeLoader.LoadMCPart(ievt, false);
            }

            float nvertices = vertex.size();
            datasets[d]->eventTree()->LoadTree(ievt);
            string currentFilename = datasets[d]->eventTree()->GetFile()->GetName();
            if(previousFilename != currentFilename) {
                previousFilename = currentFilename;
                iFile++;
                cout << "File changed!!! => " << currentFilename << endl;
            }

            long int currentRun = event->runId();

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
            else if(!isData && Muon)
            {
                if(!event->getHBHENoiseFilter()
                    || !event->getHBHENoiseIsoFilter()
                    || !event->getglobalTightHalo2016Filter()
                    || !event->getEcalDeadCellTriggerPrimitiveFilter()
                    || !event->getPVFilter()
                    || !event->getBadChCandFilter()
                    || !event->getBadPFMuonFilter())
                continue;
            }

            eventCount++;

            if(!isData){
                ttXtype = event->getgenTTX_id();
                if(dataSetName.find("TTJets")!=string::npos){
                    
                    if (ttXtype % 100 > 50) {
                        ttXrew  = 4.0/3.2;      //see TOP-16-10 for cross sections
                        ttXrew_up = (5.43) / (2.8);
                        ttXrew_down = (2.57) / (3.6);
                    }
                    if (ttXtype % 100 == 0) {       //see https://twiki.cern.ch/twiki/bin/view/CMSPublic/GenHFHadronMatcher#Event_categorization_example_2
                        ttXrew  = 184./257.;
                        ttXrew_up = (184.0 + 33.54) / (257. - 26.);
                        ttXrew_down = (184.0 - 33.54) / (257. + 26.);
                    }
                }

                if(event->getWeight(1)!= -9999){
                    centralWeight = (event->getWeight(1))/(abs(event->originalXWGTUP()));
                    weight1 = (event->getWeight(2))/(abs(event->originalXWGTUP()));
                    weight2 = (event->getWeight(3))/(abs(event->originalXWGTUP()));
                    weight3 = (event->getWeight(4))/(abs(event->originalXWGTUP()));
                    weight4 = (event->getWeight(5))/(abs(event->originalXWGTUP()));
                    weight5 = (event->getWeight(6))/(abs(event->originalXWGTUP()));
                    weight6 = (event->getWeight(7))/(abs(event->originalXWGTUP()));
                    weight7 = (event->getWeight(8))/(abs(event->originalXWGTUP()));
                    weight8 = (event->getWeight(9))/(abs(event->originalXWGTUP()));
                } else if (event->getWeight(1001)!= -9999){
                    centralWeight = (event->getWeight(1001))/(abs(event->originalXWGTUP()));
                    weight1 = (event->getWeight(1002))/(abs(event->originalXWGTUP()));
                    weight2 = (event->getWeight(1003))/(abs(event->originalXWGTUP()));
                    weight3 = (event->getWeight(1004))/(abs(event->originalXWGTUP()));
                    weight4 = (event->getWeight(1005))/(abs(event->originalXWGTUP()));
                    weight5 = (event->getWeight(1006))/(abs(event->originalXWGTUP()));
                    weight6 = (event->getWeight(1007))/(abs(event->originalXWGTUP()));
                    weight7 = (event->getWeight(1008))/(abs(event->originalXWGTUP()));
                    weight8 = (event->getWeight(1009))/(abs(event->originalXWGTUP()));
                    if (dataSetName.find("tttt")!=string::npos) {
                        weight6 = weight5;
                        weight8 = weight7;
                    }
                }

                if (event->getWeight(1001)!= -9999 && dataSetName.find("TTJets")!=string::npos) {
                    weight_hdamp_up = event->getWeight(5019)/fabs(event->originalXWGTUP());
                    weight_hdamp_dw = event->getWeight(5010)/fabs(event->originalXWGTUP());

                    weight_ct10 = event->getWeight(3001)/fabs(event->originalXWGTUP());
                    weight_mmht14 = event->getWeight(4001)/fabs(event->originalXWGTUP());
                }
            }


            float rho = event->fixedGridRhoFastjetAll();
            if(debug) cout << "Rho: " << rho << endl;



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
                    else {cerr << "Error" << endl; exit(1);}
                }
                else if(Muon && Electron){
                    if(medataset) trigged = ME;
                    else {cerr << "Error" << endl; exit(1);}
                }
                else if(!Muon && Electron){
                    if(eedataset) trigged = EE;
                    else {cerr << "Error" << endl; exit(1);}
                }
                else {cerr << "Error" << endl; exit(1);}
            } else {
                if(Muon && !Electron) trigged = MM;
                else if(Muon && Electron) trigged = ME;
                else if(!Muon && Electron) trigged = EE;
                else {cerr << "Error" << endl; exit(1);}
            }
 
            if(debug) cout << "triggered? Y/N?  " << trigged << endl;
 

            //////////////////////////////////////
            ///  Jet Energy Scale Corrections  ///
            //////////////////////////////////////
            

            if(applyJER && !isData) {
                jetTools->correctJetJER(init_jets, genjets, mets[0], "nominal", false);
            }


            if(applyJEC) {
                jetTools->correctJets(init_jets, event->fixedGridRhoFastjetAll(), isData);
            }


            float MET = mets[0]->Pt();

            //////////////////////////////////
            //      Event selection         //
            //////////////////////////////////

            // Declare selection instance
            Run2Selection selection(init_jets, init_fatjets, init_muons, init_electrons, mets, rho);
            selectedMuons.clear(); selectedElectrons.clear(); selectedOrigElectrons.clear(); selectedVetoElectrons.clear(); selectedOrigVetoElectrons.clear();
            // Define object selection cuts
            if(Muon && Electron && dilepton) {
                selectedMuons = selection.GetSelectedMuons(0., 2.4, 0.4, "Loose", "Summer16");
                selectedLooseMuons = selection.GetSelectedMuons(20., 2.4, 0.15, "Loose", "Summer16");
                selectedOrigElectrons = selection.GetSelectedElectrons(20., 2.4, "Loose", "Spring16_80X", true, true);
                selectedOrigVetoElectrons = selection.GetSelectedElectrons(15., 2.4, "Veto", "Spring16_80X", true, true);
            } if(Muon && !Electron && dilepton) {
                selectedMuons = selection.GetSelectedMuons(0., 2.4, 0.4, "Loose", "Summer16");
                selectedLooseMuons = selection.GetSelectedMuons(20., 2.4, 0.15, "Loose", "Summer16");
                selectedOrigElectrons = selection.GetSelectedElectrons(20., 2.4, "Loose", "Spring16_80X", true, true);
                selectedOrigVetoElectrons = selection.GetSelectedElectrons(15., 2.4, "Veto", "Spring16_80X", true, true);
            } if(!Muon && Electron && dilepton) {
                selectedMuons = selection.GetSelectedMuons(20., 2.4, 0.4, "Loose", "Summer16");
                selectedLooseMuons = selection.GetSelectedMuons(20., 2.4, 0.15, "Loose", "Summer16");
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

            if(Muon && !Electron && dilepton){
                if(selectedMuons.size()!=2) continue;
                if(selectedMuons[0]->Pt()<25.) continue;
            }

            if(!Muon && Electron && dilepton && selectedElectrons.size() > 0 && selectedElectrons[0]->Pt() < 25.0) continue;
            if(Muon && Electron && dilepton){
                if(selectedMuons.size() > 0 && selectedElectrons.size() == 0 && selectedMuons[0]->Pt() < 25.0) continue;
                if(selectedMuons.size() == 0 && selectedElectrons.size() > 0 && selectedElectrons[0]->Pt() < 25.0) continue;
                if(selectedMuons.size() > 0 && selectedElectrons.size() > 0 && selectedMuons[0]->Pt() < 25.0 && selectedElectrons[0]->Pt() < 25.0) continue;
            }

            selectedUncleanedJets.clear();
            selectedUncleanedJets = selection.GetSelectedJets(25., 2.4, true, "Loose");
            selectedCleanedJets.clear(); selectedJets.clear();

            for(int unj = 0; unj < selectedUncleanedJets.size(); unj++) {
                bool isClose = false;
                for(int e = 0; e < selectedElectrons.size(); e++) {
                    if(selectedElectrons[e]->DeltaR(*selectedUncleanedJets[unj]) < 0.3)
                        isClose = true;
                }
                for(int mu = 0; mu < selectedLooseMuons.size(); mu++) {
                    if(selectedLooseMuons[mu]->DeltaR(*selectedUncleanedJets[unj]) < 0.3)
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

            vector<TLorentzVector> selectedMuonsTLV_JC, selectedElectronsTLV_JC;
            vector<TLorentzVector> mcParticlesTLV, selectedJetsTLV, mcMuonsTLV, mcPartonsTLV;
            vector<TRootMCParticle*> mcParticlesMatching_;
            vector<int> mcMuonIndex, mcPartonIndex;
            JetPartonMatching muonMatching, jetMatching;

            ////////////////////////////////////
            // Preselection Lepton Operations //
            ////////////////////////////////////

            float diLepMass = 0, diMuMass = 0;
            bool ZVeto = false, sameCharge = false;
            float ZMass = 91, ZMassWindow = 15;
            int cj1 = 0, cj2 = 0, lidx1 = 0, lidx2 = 0;
            TLorentzVector lep1, lep2, diLep;
            vector<pair<float, pair<TRootLepton*, TRootLepton*> > > LeptonPairs;

            for(int selmu = 0; selmu < selectedMuons.size(); selmu++) {
                selectedMuonsTLV_JC.push_back(*selectedMuons[selmu]);
            }

            //sort(selectedPosMuons.begin(), selectedPosMuons.end(), HighestPt());
            //sort(selectedNegMuons.begin(), selectedNegMuons.end(), HighestPt());

            for(int selel = 0; selel < selectedElectrons.size(); selel++) {
                selectedElectronsTLV_JC.push_back(*selectedElectrons[selel]);
            }
            for(Int_t seljet = 0; seljet < selectedJets.size(); seljet++) {
                selectedJetsTLV.push_back(*selectedJets[seljet]);
            }

            if(nMu == 2 && nEl == 0 && Muon && !Electron) // Di-Muon Selection
            {
                lep1 = selectedMuonsTLV_JC[0];
                lep2 = selectedMuonsTLV_JC[1];
                if(selectedMuons[0]->charge() == selectedMuons[1]->charge())
                    sameCharge = true;
                nLep = nMu;
            } else if(nEl == 2 && nMu == 0 && Electron && !Muon) // Di-Electron Selection criteria
            {
                lep1 = selectedElectronsTLV_JC[0];
                lep2 = selectedElectronsTLV_JC[1];
                if(selectedElectrons[0]->charge() == selectedElectrons[1]->charge())
                    sameCharge = true;
                nLep = nEl;
            } else if(nEl == 1 && nMu == 1 && Electron && Muon) // Muon-Electron Selection
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
            } else continue;

            float temp_HT = 0., HTb = 0.;
            int jet_flavor;
            double JetPt, JetEta;

            for(Int_t seljet = 0; seljet < selectedJets.size(); seljet++) {
                jet_flavor = selectedJets[seljet]->hadronFlavour();
                JetPt = selectedJets[seljet]->Pt();
                JetEta = selectedJets[seljet]->Eta();
                temp_HT += JetPt;
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

            if(Muon && !Electron && dilepton)
                if(diLepMass < 20 || (diLepMass > (ZMass - ZMassWindow) && diLepMass < (ZMass + ZMassWindow) ))
                    ZVeto = true;

            float nJets = selectedJets.size();
            float nMtags = selectedMBJets.size();
            float nLtags = selectedLBJets.size();
            float nTtags = selectedTBJets.size();

            if(debug)
                cout << " applying baseline event selection for cut table..." << endl;
            bool isGoodPV = selection.isPVSelected(vertex, 4, 24., 2);
            if(debug)
                cout << "PrimaryVertexBit: " << isGoodPV << " TriggerBit: " << trigged << endl;


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
                if(!(nMu == 2 && nEl == 0 && !ZVeto && !sameCharge))
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

            if(dilepton && Muon && Electron) {
                if(!(nJets >= 2 && nMtags >= 2)) continue;
                if(!(nJets >= 4)) continue;
                if(!(temp_HT >= 300)) continue;
            } else if(dilepton && Muon && !Electron) {
//                if(!(nJets >= 2)) continue;
//                if(!(temp_HT >= 200)) continue;
            } else if(dilepton && !Muon && Electron) {
                if(!(nJets >= 2 && nMtags >= 2)) continue;
                if(!(nJets >= 4)) continue;
                if(!(temp_HT >= 500)) continue;
            }
            if(debug)
                cout << "Selection Passed." << endl;
            passed++;

            if(!isData && dataSetName.find("TTJets")!=string::npos) {
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
                    ){
                        n_genleps++;
                    }
                }
                if(dataSetName.find("new")!=string::npos) flag_ = 0.0902;
                else if(genHT>=500&&n_genjets>=7&&n_genleps>=2) continue;
            }


            /////////////////////////////////////////////////
            //               Pu reweighting                //
            /////////////////////////////////////////////////

            float lumiWeight;
            if(isData) {
                lumiWeight = 1;
            } else {
                lumiWeight = LumiWeights.ITweight((int)event->nTruePU());
            }

            /////////////////////////////////////////////////
            //                    bTag SF                  //
            /////////////////////////////////////////////////

            float bTagEff(1);

            if (debug) cout<<"get MC Event Weight for btag"<<endl;
            float btagWeight = 1;
            float btagWeightCSV = 1;


            //csv discriminator reweighting
            if(bTagCSVReweight && !isData){
            //get btag weight info
                for(int jetbtag = 0; jetbtag<selectedJets.size(); jetbtag++){
                    float jetpt = selectedJets[jetbtag]->Pt();
                    float jeteta = selectedJets[jetbtag]->Eta();
                    float jetdisc = selectedJets[jetbtag]->btag_combinedInclusiveSecondaryVertexV2BJetTags();
                    bool isBFlav = false;
                    bool isCFlav = false;
                    if(jetdisc<0.0) jetdisc = -0.05;
                    if(jetdisc>1.0) jetdisc = 1.0;
                    BTagEntry::JetFlavor jflav;
                    int jethadronflav = std::abs(selectedJets[jetbtag]->hadronFlavour());
                    if(debug) cout<<"hadron flavour: "<<jethadronflav<<"  jet eta: "<<jeteta<<" jet pt: "<<jetpt<<"  jet disc: "<<jetdisc<<endl;
                    if(jethadronflav == 5){
                        jflav = BTagEntry::FLAV_B;
                        isBFlav =true;
                    }
                    else if(jethadronflav == 4){
                        jflav = BTagEntry::FLAV_C;
                        isCFlav=true;
                    }
                    else{
                        jflav = BTagEntry::FLAV_UDSG;
                    }
                    bTagEff = reader_csvv2->eval(jflav, jeteta, jetpt, jetdisc);

                    btagWeightCSV*=bTagEff;
             
                    if(debug) cout<<"btag efficiency = "<<bTagEff<<endl;       
                }      


            }

            ///////////////////////////
            //  Lepton Scale Factors //
            ///////////////////////////

            float fleptonSF1 = 1., fleptonSF2 = 1.;
            float fleptonSF_GH = 1., fleptonSF_BCDEF = 1., fleptonSF = 1.;
            float SFtrigger = 1, SFtrigger_up = 1, SFtrigger_down = 1;

            if(bLeptonSF && !isData) {
                if(Muon && !Electron && nMu == 2 && nEl == 0) {
                    fleptonSF1 = muonSFWeightID_GH->at(selectedMuons[0]->Eta(), selectedMuons[0]->Pt(), 0) *
				 muonSFWeightIso_GH->at(selectedMuons[0]->Eta(), selectedMuons[0]->Pt(), 0) * 
				 h_muonSFWeightTrack->Eval(selectedMuons[0]->Eta());
                    fleptonSF2 = muonSFWeightID_GH->at(selectedMuons[1]->Eta(), selectedMuons[1]->Pt(), 0) *
				 muonSFWeightIso_GH->at(selectedMuons[1]->Eta(), selectedMuons[1]->Pt(), 0) * 
				 h_muonSFWeightTrack->Eval(selectedMuons[1]->Eta());
                    fleptonSF_GH = fleptonSF1 * fleptonSF2;
                    fleptonSF1 = muonSFWeightID_BCDEF->at(selectedMuons[0]->Eta(), selectedMuons[0]->Pt(), 0) *
				 muonSFWeightIso_BCDEF->at(selectedMuons[0]->Eta(), selectedMuons[0]->Pt(), 0) * 
                                 h_muonSFWeightTrack->Eval(selectedMuons[0]->Eta());
                    fleptonSF2 = muonSFWeightID_BCDEF->at(selectedMuons[1]->Eta(), selectedMuons[1]->Pt(), 0) *
				 muonSFWeightIso_BCDEF->at(selectedMuons[1]->Eta(), selectedMuons[1]->Pt(), 0) * 
                                 h_muonSFWeightTrack->Eval(selectedMuons[1]->Eta());
                    fleptonSF_BCDEF = fleptonSF1 * fleptonSF2;
                } else if(nEl == 2 && nMu == 0 && Electron && !Muon) {
                    fleptonSF1 = electronSFWeight->at(selectedElectrons[0]->Eta(), selectedElectrons[0]->Pt(), 0) *
				 electronSFWeightReco->at(selectedElectrons[0]->Eta(), selectedElectrons[0]->Pt(), 0);
                    fleptonSF2 = electronSFWeight->at(selectedElectrons[1]->Eta(), selectedElectrons[1]->Pt(), 0) *
				 electronSFWeightReco->at(selectedElectrons[1]->Eta(), selectedElectrons[1]->Pt(), 0);
                    fleptonSF_GH = fleptonSF1 * fleptonSF2;
                    fleptonSF_BCDEF = fleptonSF1 * fleptonSF2;
                } else if(Electron && Muon && nEl == 1 && nMu == 1) {
                    fleptonSF1 = electronSFWeight->at(selectedElectrons[0]->Eta(), selectedElectrons[0]->Pt(), 0) *
				 electronSFWeightReco->at(selectedElectrons[0]->Eta(), selectedElectrons[0]->Pt(), 0);
                    fleptonSF2 = muonSFWeightID_GH->at(selectedMuons[0]->Eta(), selectedMuons[0]->Pt(), 0) *
				 muonSFWeightIso_GH->at(selectedMuons[0]->Eta(), selectedMuons[0]->Pt(), 0) * 
                                 h_muonSFWeightTrack->Eval(selectedMuons[0]->Eta());
                    fleptonSF_GH = fleptonSF1 * fleptonSF2;
                    fleptonSF2 = muonSFWeightID_BCDEF->at(selectedMuons[0]->Eta(), selectedMuons[0]->Pt(), 0) *
				 muonSFWeightIso_BCDEF->at(selectedMuons[0]->Eta(), selectedMuons[0]->Pt(), 0) * 
                                 h_muonSFWeightTrack->Eval(selectedMuons[0]->Eta());
                    fleptonSF_BCDEF = fleptonSF1 * fleptonSF2;
                }
                fleptonSF = (19676.2598077*fleptonSF_BCDEF + 16146.1775979*fleptonSF_GH)/(35822.4374055);
                float eta1, eta2;
                if(Muon && !Electron){
		    eta1 = selectedMuons[0]->Eta();
		    eta2 = selectedMuons[1]->Eta();
                    if(abs(eta1) < 1.2){
                        if(abs(eta2) < 1.2){
                            SFtrigger = 0.991; SFtrigger_up = 0.992; SFtrigger_down = 0.990;
                        } else if(abs(eta2) < 2.4){
                            SFtrigger = 0.990; SFtrigger_up = 0.993; SFtrigger_down = 0.987;
                        } else {cerr << "Error2" << endl; exit(1);}
                    } else if(abs(eta1) < 2.4){
                        if(abs(eta2) < 1.2){
                            SFtrigger = 0.995; SFtrigger_up = 0.998; SFtrigger_down = 0.992;
                        } else if(abs(eta2) < 2.4){
                            SFtrigger = 0.987; SFtrigger_up = 0.990; SFtrigger_down = 0.984;
                        } else {cerr << "Error2" << endl; exit(1);}
                    } else {cerr << "Error1" << endl; exit(1);}
                } else if(Muon && Electron){
                    if(selectedMuons[0]->Pt() > selectedElectrons[0]->Pt()) {eta1 = selectedMuons[0]->Eta(); eta2 = selectedElectrons[0]->Eta();}
                    else {eta2 = selectedMuons[0]->Eta(); eta1 = selectedElectrons[0]->Eta();}
                    if(abs(eta1) < 1.2){
                        if(abs(eta2) < 1.2){
                            SFtrigger = 0.996; SFtrigger_up = 0.997; SFtrigger_down = 0.995;
                        } else if(abs(eta2) < 2.4){
                            SFtrigger = 0.999; SFtrigger_up = 1.002; SFtrigger_down = 0.996;
                        } else {cerr << "Error2" << endl; exit(1);}
                    } else if(abs(eta1) < 2.4){
                        if(abs(eta2) < 1.2){
                            SFtrigger = 0.995; SFtrigger_up = 0.998; SFtrigger_down = 0.992;
                        } else if(abs(eta2) < 2.4){
                            SFtrigger = 0.990; SFtrigger_up = 0.996; SFtrigger_down = 0.984;
                        } else {cerr << "Error2" << endl; exit(1);}
                    } else {cerr << "Error1" << endl; exit(1);}
                } else if(!Muon && Electron){
                    eta1 = selectedElectrons[0]->Eta();
                    eta2 = selectedElectrons[1]->Eta();
                    if(abs(eta1) < 1.2){
                        if(abs(eta2) < 1.2){
                            SFtrigger = 0.990; SFtrigger_up = 0.992; SFtrigger_down = 0.988;
                        } else if(abs(eta2) < 2.4){
                            SFtrigger = 0.990; SFtrigger_up = 0.987; SFtrigger_down = 0.993;
                        } else {cerr << "Error2" << endl; exit(1);}
                    } else if(abs(eta1) < 2.4){
                        if(abs(eta2) < 1.2){
                            SFtrigger = 0.995; SFtrigger_up = 0.998; SFtrigger_down = 0.992;
                        } else if(abs(eta2) < 2.4){
                            SFtrigger = 0.979; SFtrigger_up = 0.986; SFtrigger_down = 0.972;
                        } else {cerr << "Error2" << endl; exit(1);}
                    } else {cerr << "Error1" << endl; exit(1);}
                }
            }
            //fleptonSF = fleptonSF1 * fleptonSF2;
            //if(debug) cout << "lepton1 SF:  " << fleptonSF1 << "  lepton2 SF:  " << fleptonSF2 << endl;
            /*if(Muon && !Electron && !isData){
                if( abs( selectedMuons[0]->Eta() )<0.9 ){
                    if( abs( selectedMuons[1]->Eta()<0.9 ) ) {
				sfleptrig_BCDEF = 0.948179;sfleptrig_GH = (7540.49*0.976139 + 8605.69*0.968985)/(7540.49+8605.69);
				sfleptrig_BCDEFUp = 0.948179;sfleptrig_GHUp = (7540.49*0.98168502 + 8605.69*0.9749255)/(7540.49+8605.69);
				sfleptrig_BCDEFDown = 0.948179;sfleptrig_GHDown = (7540.49*0.97059298 + 8605.69*0.9630445)/(7540.49+8605.69);
                    } else if( abs( selectedMuons[1]->Eta()<1.2 ) ) {
				sfleptrig_BCDEF = 0.960657;sfleptrig_GH = (7540.49*0.980864 + 8605.69*0.979902)/(7540.49+8605.69);
	                        sfleptrig_BCDEFUp = 0.960657;sfleptrig_GHUp = (7540.49*0.98934893 + 8605.69*0.98890021)/(7540.49+8605.69);		
				sfleptrig_BCDEFDown = 0.960657;sfleptrig_GHDown = (7540.49*0.97237907 + 8605.69*0.97090379)/(7540.49+8605.69);
		    } else if( abs( selectedMuons[1]->Eta()<2.1 ) ) {
				sfleptrig_BCDEF = 0.968998;sfleptrig_GH = (7540.49*0.990586 + 8605.69*0.986834)/(7540.49+8605.69);
				sfleptrig_BCDEFUp = 0.968998;sfleptrig_GHUp = (7540.49*0.99660106 + 8605.69*0.99343632)/(7540.49+8605.69);
				sfleptrig_BCDEFDown = 0.968998;sfleptrig_GHDown = (7540.49*0.98457094 + 8605.69*0.98023168)/(7540.49+8605.69);
                    } else if( abs( selectedMuons[1]->Eta()<2.4 ) ) {
				sfleptrig_BCDEF = 0.960431;sfleptrig_GH = (7540.49*0.985026 + 8605.69*0.978097)/(7540.49+8605.69);
				sfleptrig_BCDEFUp = 0.960431;sfleptrig_GHUp = (7540.49*0.997788 + 8605.69*0.9956252)/(7540.49+8605.69);
				sfleptrig_BCDEFDown = 0.960431;sfleptrig_GHDown = (7540.49*0.972264 + 8605.69*0.9605688)/(7540.49+8605.69);
                    } else {cerr << "Error" << endl; exit(1);}
                } else if( abs( selectedMuons[0]->Eta() )<1.2 ) {
                    if( abs( selectedMuons[1]->Eta()<0.9 ) ) {
				sfleptrig_BCDEF = 0.955935;sfleptrig_GH = (7540.49*0.982464 + 8605.69*0.983213)/(7540.49+8605.69);
                                sfleptrig_BCDEFUp = 0.955935;sfleptrig_GHUp = (7540.49*0.99094986 + 8605.69*0.99220793)/(7540.49+8605.69);
                                sfleptrig_BCDEFDown = 0.955935;sfleptrig_GHDown = (7540.49*0.97397814 + 8605.69*0.97421807)/(7540.49+8605.69);
                    } else if( abs( selectedMuons[1]->Eta()<1.2 ) ) {
				sfleptrig_BCDEF = 0.964931;sfleptrig_GH = (7540.49*1.016780 + 8605.69*0.999540)/(7540.49+8605.69);
                                sfleptrig_BCDEFUp = 0.964931;sfleptrig_GHUp = (7540.49*1.02067743 + 8605.69*1.0106039)/(7540.49+8605.69);
                                sfleptrig_BCDEFDown = 0.964931;sfleptrig_GHDown = (7540.49*1.01288257 + 8605.69*0.9884761)/(7540.49+8605.69);
                    } else if( abs( selectedMuons[1]->Eta()<2.1 ) ) {
				sfleptrig_BCDEF = 0.982130;sfleptrig_GH = (7540.49*0.991973 + 8605.69*0.991456)/(7540.49+8605.69);
                                sfleptrig_BCDEFUp = 0.982130;sfleptrig_GHUp = (7540.49*0.9994536 + 8605.69*1.00077573)/(7540.49+8605.69);
                                sfleptrig_BCDEFDown = 0.982130;sfleptrig_GHDown = (7540.49*0.9844924 + 8605.69*0.98213627)/(7540.49+8605.69);
                    } else if( abs( selectedMuons[1]->Eta()<2.4 ) ) {
				sfleptrig_BCDEF = 0.951884;sfleptrig_GH = (7540.49*1.004301 + 8605.69*0.999805)/(7540.49+8605.69);
                                sfleptrig_BCDEFUp = 0.951884;sfleptrig_GHUp = (7540.49*1.0205237 + 8605.69*1.018131)/(7540.49+8605.69);
                                sfleptrig_BCDEFDown = 0.951884;sfleptrig_GHDown = (7540.49*0.9880783 + 8605.69*0.981479)/(7540.49+8605.69);
                    } else {cerr << "Error" << endl; exit(1);}
                } else if( abs( selectedMuons[0]->Eta() )<2.1 ) {
                    if( abs( selectedMuons[1]->Eta()<0.9 ) ) {
				sfleptrig_BCDEF = 0.970120;sfleptrig_GH = (7540.49*0.988191 + 8605.69*0.983700)/(7540.49+8605.69);
                                sfleptrig_BCDEFUp = 0.970120;sfleptrig_GHUp = (7540.49*0.99418715 + 8605.69*0.99040486)/(7540.49+8605.69);
                                sfleptrig_BCDEFDown = 0.970120;sfleptrig_GHDown = (7540.49*0.98219485 + 8605.69*0.97699514)/(7540.49+8605.69);
                    } else if( abs( selectedMuons[1]->Eta()<1.2 ) ) {
				sfleptrig_BCDEF = 0.979653;sfleptrig_GH = (7540.49*0.992394 + 8605.69*0.982809)/(7540.49+8605.69);
                                sfleptrig_BCDEFUp = 0.979653;sfleptrig_GHUp = (7540.49*1.00021733 + 8605.69*0.99246931)/(7540.49+8605.69);
                                sfleptrig_BCDEFDown = 0.979653;sfleptrig_GHDown = (7540.49*0.98457067 + 8605.69*0.97314869)/(7540.49+8605.69);
                    } else if( abs( selectedMuons[1]->Eta()<2.1 ) ) {
				sfleptrig_BCDEF = 0.991621;sfleptrig_GH = (7540.49*0.994308 + 8605.69*0.976385)/(7540.49+8605.69);
                                sfleptrig_BCDEFUp = 0.991621;sfleptrig_GHUp = (7540.49*1.00070344 + 8605.69*0.9874707)/(7540.49+8605.69);
                                sfleptrig_BCDEFDown = 0.991621;sfleptrig_GHDown = (7540.49*0.98791256 + 8605.69*0.9652993)/(7540.49+8605.69);
                    } else if( abs( selectedMuons[1]->Eta()<2.4 ) ) {
				sfleptrig_BCDEF = 0.983483;sfleptrig_GH = (7540.49*0.989969 + 8605.69*0.983709)/(7540.49+8605.69);
                                sfleptrig_BCDEFUp = 0.983483;sfleptrig_GHUp = (7540.49*1.000219 + 8605.69*0.9956063)/(7540.49+8605.69);
                                sfleptrig_BCDEFDown = 0.983483;sfleptrig_GHDown = (7540.49*0.979719 + 8605.69*0.9718117)/(7540.49+8605.69);
                    } else {cerr << "Error" << endl; exit(1);}
                } else if( abs( selectedMuons[0]->Eta() )<2.4 ) {
                    if( abs( selectedMuons[1]->Eta()<0.9 ) ) {
				sfleptrig_BCDEF = 0.970599;sfleptrig_GH = (7540.49*0.990155 + 8605.69*0.979211)/(7540.49+8605.69);
                                sfleptrig_BCDEFUp = 0.970599;sfleptrig_GHUp = (7540.49*1.0032201 + 8605.69*0.9953345)/(7540.49+8605.69);
                                sfleptrig_BCDEFDown = 0.970599;sfleptrig_GHDown = (7540.49*0.9770899 + 8605.69*0.9630875)/(7540.49+8605.69);
                    } else if( abs( selectedMuons[1]->Eta()<1.2 ) ) {
				sfleptrig_BCDEF = 0.960382;sfleptrig_GH = (7540.49*1.005147 + 8605.69*0.992346)/(7540.49+8605.69);
                                sfleptrig_BCDEFUp = 0.960382;sfleptrig_GHUp = (7540.49*1.0184711 + 8605.69*1.0105148)/(7540.49+8605.69);
                                sfleptrig_BCDEFDown = 0.960382;sfleptrig_GHDown = (7540.49*0.9918289 + 8605.69*0.9741772)/(7540.49+8605.69);
                    } else if( abs( selectedMuons[1]->Eta()<2.1 ) ) {
				sfleptrig_BCDEF = 0.981527;sfleptrig_GH = (7540.49*1.000300 + 8605.69*0.992799)/(7540.49+8605.69);
                                sfleptrig_BCDEFUp = 0.981527;sfleptrig_GHUp = (7540.49*1.0099321 + 8605.69*1.0044061)/(7540.49+8605.69);
                                sfleptrig_BCDEFDown = 0.981527;sfleptrig_GHDown = (7540.49*0.9906679 + 8605.69*0.9811919)/(7540.49+8605.69);
                    } else if( abs( selectedMuons[1]->Eta()<2.4 ) ) {
				sfleptrig_BCDEF = 0.968428;sfleptrig_GH = (7540.49*0.972295 + 8605.69*0.974504)/(7540.49+8605.69);
                                sfleptrig_BCDEFUp = 0.968428;sfleptrig_GHUp = (7540.49*0.9911826 + 8605.69*0.9956983)/(7540.49+8605.69);
                                sfleptrig_BCDEFDown = 0.968428;sfleptrig_GHDown = (7540.49*0.9534074 + 8605.69*0.9533097)/(7540.49+8605.69);
                    } else {cerr << "Error" << endl; exit(1);}
                } else {cerr << "Error" << endl; exit(1);}
            }*/
            /*else if(Muon && M && !MM && !ME && !isData){
                sfleptrig_BCDEF = muonSFWeightTrig_BCDEF->at(selectedMuons[0]->Eta(), selectedMuons[0]->Pt(), 0);
                sfleptrig_GH = muonSFWeightTrig_GH->at(selectedMuons[0]->Eta(), selectedMuons[0]->Pt(), 0);
            }*/


            if(!isData){
                mcParticlesMatching_.clear();
                treeLoader.LoadMCEvent(ievt, 0, mcParticlesMatching_, false);
            }

            ///////////////////////
            //  Top PT Reweight  //
            ///////////////////////

            float fTopPtsf = 1, fAntitopPtsf = 1, fTopPtReWeightsf = 1,
                  fTopPtsfUp = 1, fAntitopPtsfUp = 1, fTopPtReWeightsfUp = 1,
                  fTopPtsfDown = 1, fAntitopPtsfDown = 1, fTopPtReWeightsfDown = 1;
            int nTops = 0, nAntiTops = 0;
            if(dataSetName.find("TTJets") != string::npos || dataSetName.find("TTJetsMG") != string::npos) {
                for(int part = 0; part < mcParticlesMatching_.size(); part++) {
                    if(mcParticlesMatching_[part]->type() == 6 && 
                       //mcParticlesMatching_[part]->status() == 22 &&
                       mcParticlesMatching_[part]->isLastCopy()) {
                        //if(mcParticlesMatching_[part]->Pt() < 400)
                            fTopPtsf = exp(0.0615 - (0.0005 * mcParticlesMatching_[part]->Pt()));
                            fTopPtsfUp = exp(0.0615 + 0.0324 - ((0.0005 - 0.00017) * mcParticlesMatching_[part]->Pt()));
                            fTopPtsfDown = exp(0.0615 - 0.0324 - ((0.0005 + 0.00017) * mcParticlesMatching_[part]->Pt()));
                        //else
                        //    fTopPtsf = exp(0.0615 - (0.0005 * 400));
                        nTops++;
                    }
                    else if(mcParticlesMatching_[part]->type() == -6 &&
                            //mcParticlesMatching_[part]->status() == 22 &&
                            mcParticlesMatching_[part]->isLastCopy()) {
                        //if(mcParticlesMatching_[part]->Pt() < 400)
                            fAntitopPtsf = exp(0.0615 - (0.0005 * mcParticlesMatching_[part]->Pt()));
                            fAntitopPtsfUp = exp(0.0615 + 0.0324 - ((0.0005 - 0.00017) * mcParticlesMatching_[part]->Pt()));
                            fAntitopPtsfDown = exp(0.0615 - 0.0324 - ((0.0005 + 0.00017) * mcParticlesMatching_[part]->Pt()));
                        //else
                        //    fAntitopPtsf = exp(0.0615 - (0.0005 * 400));
                        nAntiTops++; 
                    }
                }
                fTopPtReWeightsf = sqrt(fTopPtsf * fAntitopPtsf);
                fTopPtReWeightsfUp = sqrt(fTopPtsfUp * fAntitopPtsfUp);
                fTopPtReWeightsfDown = sqrt(fTopPtsfDown * fAntitopPtsfDown);
            }



            float reliso1, reliso2;
            if(dilepton && Muon && Electron) {
                lep1Pt = selectedMuons[0]->Pt();
                lep2Pt = selectedElectrons[0]->Pt();
                reliso1 = selectedMuons[0]->relPfIso(4,0.5);
                reliso2 = ElectronRelIso(selectedElectrons[0],rho);

            }
            if(dilepton && Muon && !Electron) {
                lep1Pt = selectedMuons[0]->Pt();
                lep2Pt = selectedMuons[1]->Pt();
                reliso1 = selectedMuons[0]->relPfIso(4,0.5);
                reliso2 = selectedMuons[1]->relPfIso(4,0.5);

            }
            if(dilepton && !Muon && Electron) {
                lep1Pt = selectedElectrons[0]->Pt();
                lep2Pt = selectedElectrons[1]->Pt();
                reliso1 = ElectronRelIso(selectedElectrons[0],rho);
                reliso2 = ElectronRelIso(selectedElectrons[1],rho);

            }
            scaleFactor = SFtrigger*fleptonSF*btagWeightCSV*lumiWeight*fTopPtReWeightsf*ttXrew*centralWeight*flag_;

            ////////////////////
            // Filling nTuple //
            //////////////////// 
 
            float vals[8] = {lep1Pt, lep2Pt, reliso1, reliso2, nJets, temp_HT, MET, scaleFactor};

            tup->Fill(vals);
        } // End Loop on Events

        tupfile->cd();
        tup->Write();
        tupfile->Close();

        cout << "n events passing selection  = " << passed << endl;
        cout << "n events passing trigger    = " << trigCount << endl;
        cout << "n events passing filter     = " << eventCount << endl;
        cout << "trigger eff. = " << (float) trigCount/(float) eventCount << endl;

        treeLoader.UnLoadDataset(); // important: free memory
    }
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

float PythiaTune(int jets)
{
    float sf = 1;

    if(jets == 0)
        sf = 0.9747749;
    else if(jets == 1)
        sf = 0.9764329;
    else if(jets == 2)
        sf = 0.9733197;
    else if(jets == 3)
        sf = 0.9815515;
    else if(jets == 4)
        sf = 0.9950933;
    else if(jets == 5)
        sf = 1.0368650;
    else if(jets == 6)
        sf = 1.1092038;
    else if(jets == 7)
        sf = 1.1842445;
    else if(jets == 8)
        sf = 1.3019452;
    else if(jets == 9)
        sf = 1.1926751;
    else if(jets >= 10)
        sf = 1.5920859;

    return sf;
}
