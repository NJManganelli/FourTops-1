#include "TStyle.h"
#include "TPaveText.h"

#include <cmath>
#include <fstream>
#include <sstream>
#include <sys/stat.h>
#include <string>
#include "TRandom3.h"
#include "TNtuple.h"

// user code
#include "TopTreeProducer/interface/TRootRun.h"
#include "TopTreeProducer/interface/TRootEvent.h"
#include "TopTreeAnalysisBase/Selection/interface/SelectionTable.h"
#include "TopTreeAnalysisBase/Content/interface/AnalysisEnvironment.h"
#include "TopTreeAnalysisBase/Tools/interface/TTreeLoader.h"
#include "TopTreeAnalysisBase/tinyxml/tinyxml.h"
#include "TopTreeAnalysisBase/Tools/interface/MultiSamplePlot.h"
//#include "../macros/Style.C"

#include <sstream>
#include <algorithm>

using namespace std;
using namespace TopTree;

/// Normal Plots (TH1F* and TH2F*)
map<string, TH1F*> histo1D;
map<string, TH2F*> histo2D;
map<string, TFile*> FileObj;
map<string, TNtuple*> nTuple;
map<string, MultiSamplePlot*> MSPlot;
map<std::string, std::string> MessageMap;

bool prelim_ = true;  //controls the appearance of "preliminary on the plots"
bool split_ttbar = false;
bool reweight_ttbar = true;

std::string intToStr(int number);
void dump_to_stdout(const char* pFilename);



void DatasetPlotter(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string xmlNom,
    string CraneenPath,
    string shapefileName,
    string units);

void SplitDatasetPlotter(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string sSplitVar,
    float fbSplit,
    float ftSplit,
    float fwSplit,
    string xmlNom,
    string CraneenPath,
    string shapefileName,
    string units);

void Split2DatasetPlotter(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string sSplitVar1,
    float fbSplit1,
    float ftSplit1,
    float fwSplit1,
    string sSplitVar2,
    float fbSplit2,
    float ftSplit2,
    float fwSplit2,
    string xmlNom,
    string CraneenPath,
    string shapefileName,
    string units);

void DataCardProducer(string VoI,
    TFile* shapefile,
    string shapefileName,
    string channel,
    string leptoAbbr,
    string xmlNom,
    float lScale);
void Split_DataCardProducer(string VoI,
    TFile* shapefile,
    string shapefileName,
    string channel,
    string leptoAbbr,
    bool jetSplit,
    string sSplitVar1,
    float fbSplit1,
    float ftSplit1,
    float fwSplit1,
    string xmlNom,
    float lScale);
void Split2_DataCardProducer(string VoI,
    TFile* shapefile,
    string shapefileName,
    string channel,
    string leptoAbbr,
    bool jetSplit,
    bool jetTagsplit,
    string sSplitVar1,
    float fbSplit1,
    float ftSplit1,
    float fwSplit1,
    string sSplitVar2,
    float fbSplit2,
    float ftSplit2,
    float fwSplit2,
    string xmlNom,
    float lScale);

void GetErrorBand(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string xmlNom,
    string CraneenPath,
    string shapefileName);

void GetScaleEnvelope(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string xmlNom,
    string CraneenPath,
    string shapefileName);
void GetScaleEnvelope_tttt(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string xmlNom,
    string CraneenPath,
    string shapefileName);
void GetScaleEnvelopeSplit(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string sSplitVar,
    float fbSplit,
    float ftSplit,
    float fwSplit,
    string xmlNom,
    string CraneenPath,
    string shapefileName,
    string mainTTbarSample);
void GetScaleEnvelopeSplit_tttt(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string sSplitVar,
    float fbSplit,
    float ftSplit,
    float fwSplit,
    string xmlNom,
    string CraneenPath,
    string shapefileName,
    string mainTTbarSample);
void CutFlowPlotter(TFile* cffile,
    string leptoAbbr,
    string channel,
    string xmlNom,
    string CraneenPath,
    int nCuts,
    float lScale);

void GetPostFits(int nBins, 
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile *shapefile,
    TFile *errorfile,
    string channel, 
    string sVarofinterest, 
    string sSplitVar1, 
    float fbSplit1, 
    float ftSplit1, 
    float fwSplit1, 
    string sSplitVar2,
    float fbSplit2,
    float ftSplit2,
    float fwSplit2,
    string xmlNom,
    string CraneenPath,
    string shapefileName,
    string units);

float PythiaTune(int jets);
float findmax(float a, float b, float c);
float findmin(float a, float b, float c);

std::string plotVarNames(string s);

string DatacardVar = "BDT"; // variable of interest for plotting //global

int main(int argc, char** argv)
{
    int NumberOfBins;     // fixed width nBins
    float lumiScale = -1; // Amount of luminosity to MEScale to in fb^-1
    bool jetSplit = false, jetTagsplit = false, split_ttbar = false, postfitplots= false;
    
    int isplit_ttbar = 0;
    float lBound, uBound, bSplit, tSplit, wSplit, bSplit1, tSplit1, wSplit1, bSplit2, tSplit2,
        wSplit2; // + the bottom, top, and width of the splitting for 1 & 2 variables
    string leptoAbbr, channel, chan, xmlFileName, xmlFileNameSys, CraneenPath, splitVar, splitVar1, splitVar2, VoI,
        Units;
    string splitting = "inc";

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
        while(iarg < argc) {
            string val = argv[iarg];
            iarg++;
            if(val.find("--JTS") != std::string::npos) {
                jetTagsplit = true;
                splitting = "JTS";
                cout << "!!!!!!! doing Jet tag split !!!" << endl;
            } else if(val.find("--JS") != std::string::npos) {
                jetSplit = true;
                splitting = "JS";
                cout << "!!!!!!! doing Jet split !!!" << endl;
            } else if (val.find("--post") != string::npos){
                postfitplots = true;
                splitting = "post";
                cout<<"!!!!!!! making post fit plots !!!!!!!"<<endl;
            }
        }
    }

    string xmlstring = "config/Vars.xml";
    const char* xmlchar = xmlstring.c_str();
    TiXmlDocument doc(xmlchar);
    bool loadOkay = doc.LoadFile();
    if(loadOkay) {
        printf("\n%s:\n", xmlchar);
    } else {
        printf("Failed to load file \"%s\"\n", xmlchar);
        return 0;
    }

    // std::string slumiScale = intToStr(lumiScale);

    TiXmlHandle hDoc(&doc);
    TiXmlElement* pElem;
    TiXmlElement* qElem;
    TiXmlNode* node = 0;
    node = hDoc.Node();
    TiXmlHandle hRoot(0);
    cout << "defined" << endl;

    {
        pElem = hDoc.FirstChildElement().Element();
        hRoot = TiXmlHandle(pElem);
        // TiXmlElement* child = hRoot.FirstChild("analyses").FirstChild().Element();
        TiXmlElement* child = hDoc.FirstChild("analyses")
                                  .FirstChild("channel")
                                  .Element(); // get name of channel and check it matches input before continuing
        for(child; child; child = child->NextSiblingElement()) {
            string pName = child->Attribute("name");
            if(pName == chan) {
                cout << pName << endl;
                break;
            }
        }
        // set paths
        leptoAbbr = child->FirstChild("leptoAbbr")->ToElement()->GetText();
        channel = child->FirstChild("chan")->ToElement()->GetText();
        xmlFileName = child->FirstChild("fileName")->ToElement()->GetText();
        xmlFileNameSys = child->FirstChild("fileNameSys")->ToElement()->GetText();
        CraneenPath = child->FirstChild("craneenPath")->ToElement()->GetText();
        string temp_var = child->FirstChild("datacardVar")->ToElement()->GetText();

        if(!temp_var.empty())
            DatacardVar = temp_var;
        else
            cout << "No datacard Variable set.  Defaulting to BDT." << endl;

        // split ttbar
        // TiXmlElement* childttbarsplit = child->FirstChild( "split_ttbar" )->ToElement();
        // split_ttbar =  childttbarsplit->Attribute("split");
        // childttbarsplit->QueryIntAttribute("split", &isplit_ttbar);
        // split_ttbar = isplit_ttbar;
        // cout<<"TTBAR SPLIT "<<split_ttbar<<endl;
        cout << "leptoAbbr: " << leptoAbbr << "  channel: " << channel << "  xmlFileName: " << xmlFileName
             << "  xmlFileNameSys: " << xmlFileNameSys << "  CraneenPath: " << CraneenPath << endl;

        // Get splittings from xml depending on JS or JTS
        TiXmlElement* child3 = child->FirstChild("splitting")->ToElement();
        if(jetSplit || jetTagsplit) {
            for(child3; child3; child3 = child3->NextSiblingElement()) {
                const char* p3Key = child3->Value();
                const char* p3Text = child3->GetText();
                if(p3Key && p3Text && p3Text == splitting) {
                    cout << "splitting: " << splitting << endl;
                    break;
                }
            }
        }

        else if(postfitplots) {
            for(child3; child3; child3 = child3->NextSiblingElement()) {
                const char* p3Key = child3->Value();
                const char* p3Text = child3->GetText();
                splitting = "JTS";
                if(p3Key && p3Text && p3Text == splitting) {
                    cout << "splitting: " << "post" << endl;
                    break;
                }
            }
        }
        if(jetSplit) {
            splitVar = child3->Attribute("splitVar");
            child3->QueryFloatAttribute("bSplit", &bSplit);
            child3->QueryFloatAttribute("tSplit", &tSplit);
            child3->QueryFloatAttribute("wSplit", &wSplit);
            cout << "splitVar: " << splitVar << "  b: " << bSplit << "  t: " << tSplit << "  w: " << wSplit << endl;
        } else if(jetTagsplit || postfitplots) {
            splitVar1 = child3->Attribute("splitVar1");
            splitVar2 = child3->Attribute("splitVar2");
            child3->QueryFloatAttribute("bSplit1", &bSplit1);
            child3->QueryFloatAttribute("tSplit1", &tSplit1);
            child3->QueryFloatAttribute("wSplit1", &wSplit1);
            child3->QueryFloatAttribute("bSplit2", &bSplit2);
            child3->QueryFloatAttribute("tSplit2", &tSplit2);
            child3->QueryFloatAttribute("wSplit2", &wSplit2);
            cout << "splitVar1: " << splitVar1 << "splitVar2: " << splitVar2 << "  b1: " << bSplit1
                 << "  t1: " << tSplit1 << "  w1: " << wSplit1 << "  b2: " << bSplit2 << "  t2: " << tSplit2
                 << "  w2: " << wSplit2 << endl;
        }

        TiXmlElement* child2 = child->FirstChild("var")->ToElement();
        for(child2; child2; child2 = child2->NextSiblingElement()) {
            const char* ppKey = child2->Value();
            const char* ppText = child2->GetText();
            if(ppKey && ppText) {
                VoI = ppText;
                string shapefileName = "";
                shapefileName = "shapefile" + leptoAbbr + "_" + "DATA" + "_" + VoI + "_" + splitting + ".root";
                cout << shapefileName << endl;
                TFile* shapefile = new TFile((shapefileName).c_str(), "RECREATE");
                TFile* errorfile =
                    new TFile(("ScaleFiles" + leptoAbbr + "_light/Error" + VoI + ".root").c_str(), "RECREATE");

                child2->QueryFloatAttribute("lBound", &lBound);
                child2->QueryFloatAttribute("uBound", &uBound);
                child2->QueryIntAttribute("nBins", &NumberOfBins);
                Units = child2->Attribute("units");
                cout << "Variable : " << ppText << "  lBound : " << lBound << "   uBound : " << uBound
                     << "  nBins: " << NumberOfBins << endl;
                if(jetSplit) {
                    SplitDatasetPlotter(NumberOfBins, lumiScale, lBound, uBound, leptoAbbr, shapefile, errorfile,
                        channel, VoI, splitVar, bSplit, tSplit, wSplit, xmlFileName, CraneenPath, shapefileName, Units);
                    if(VoI.find("BDT") != string::npos || VoI.find("HT") != string::npos) {
                        Split_DataCardProducer(VoI, shapefile, shapefileName, channel, leptoAbbr, jetSplit, splitVar,
                            bSplit, tSplit, wSplit, xmlFileName, lumiScale);
                    }
                } else if(jetTagsplit) {

                    Split2DatasetPlotter(NumberOfBins, lumiScale, lBound, uBound, leptoAbbr, shapefile, errorfile,
                        channel, VoI, splitVar1, bSplit1, tSplit1, wSplit1, splitVar2, bSplit2, tSplit2, wSplit2,
                        xmlFileName, CraneenPath, shapefileName, Units);
                    //if(VoI.find("BDT") != string::npos || VoI == "HT") {
                    Split2_DataCardProducer(VoI, shapefile, shapefileName, channel, leptoAbbr, jetSplit,
                        jetTagsplit, splitVar1, bSplit1, tSplit1, wSplit1, splitVar2, bSplit2, tSplit2, wSplit2,
                        xmlFileName, lumiScale);
                    //}
                }else if(postfitplots){
                    GetPostFits(NumberOfBins, lumiScale, lBound, uBound, leptoAbbr, shapefile, errorfile,
                        channel, VoI, splitVar1, bSplit1, tSplit1, wSplit1, splitVar2, bSplit2, tSplit2, wSplit2,
                        xmlFileName, CraneenPath, shapefileName, Units);
                } else {
                    DatasetPlotter(NumberOfBins, lumiScale, lBound, uBound, leptoAbbr, shapefile, errorfile, channel,
                        VoI, xmlFileName, CraneenPath, shapefileName, Units);
                    //if(VoI.find("BDT") != string::npos) {
                    //    DataCardProducer(VoI, shapefile, shapefileName, channel, leptoAbbr, xmlFileName, lumiScale);
                    //}
                }

                shapefile->Close();

                // errorfile->Close();

                delete shapefile;
                delete errorfile;
                cout << "" << endl;
                cout << "end var" << endl;
            }
        }
    }
//        string cffileName = "Cut_Flow_" + leptoAbbr + ".root";
//        cout << cffileName << endl;
//        TFile* cffile = new TFile((cffileName).c_str(), "RECREATE");
//        CutFlowPlotter(cffile, leptoAbbr, channel, xmlFileName, CraneenPath, 9, lumiScale);
//        delete cffile;
    cout << " DONE !! " << endl;
}

void GetErrorBand(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string xmlNom,
    string CraneenPath,
    string shapefileName,
    string mainTTbarSample)
{
    cout << "Producing Error Band for ttbar" << endl;
    histo1D["weightPlus"] = new TH1F("ErrPlus", "Plus", nBins, plotLow, plotHigh);
    histo1D["weightMinus"] = new TH1F("ErrMinus", "Minus", nBins, plotLow, plotHigh);

    string sysname = channel + "__" + "ttbarTTX" + "__";

    histo1D["weight0"] = (TH1F*)shapefile->Get("Genweight_tt");
    histo1D["weight1"] = (TH1F*)shapefile->Get("weight1_tt");
    histo1D["weight2"] = (TH1F*)shapefile->Get("weight2_tt");
    histo1D["weight3"] = (TH1F*)shapefile->Get("weight3_tt");
    histo1D["weight4"] = (TH1F*)shapefile->Get("weight4_tt");
    histo1D["weight5"] = (TH1F*)shapefile->Get("weight5_tt");
    histo1D["weight6"] = (TH1F*)shapefile->Get("weight6_tt");
    histo1D["weight7"] = (TH1F*)shapefile->Get("weight7_tt");
    histo1D["weight8"] = (TH1F*)shapefile->Get("weight8_tt");

    histo1D["err2Up"] = (TH1F*)shapefile->Get((sysname + "PUUp").c_str());
    histo1D["err3Up"] = (TH1F*)shapefile->Get((sysname + "TTJets_HDAMPUp").c_str());
    histo1D["err4Up"] = (TH1F*)shapefile->Get((sysname + "heavyFlavUp").c_str());
    histo1D["err5Up"] = (TH1F*)shapefile->Get((sysname + "JERUp").c_str());
    histo1D["err6Up"] = (TH1F*)shapefile->Get((sysname + "JESUp").c_str());
    histo1D["err7Up"] = (TH1F*)shapefile->Get((sysname + "TTUEUp").c_str());
    histo1D["err8Up"] = (TH1F*)shapefile->Get((sysname + "TTISRUp").c_str());
    histo1D["err9Up"] = (TH1F*)shapefile->Get((sysname + "TTFSRUp").c_str());
    histo1D["err10Up"] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVLFUp").c_str());
    histo1D["err11Up"] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVHFUp").c_str());
    histo1D["err12Up"] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVHFStats1Up").c_str());
    histo1D["err13Up"] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVHFStats2Up").c_str());
    histo1D["err14Up"] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVLFStats1Up").c_str());
    histo1D["err15Up"] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVLFStats2Up").c_str());
    histo1D["err16Up"] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVCFErr1Up").c_str());
    histo1D["err17Up"] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVCFErr2Up").c_str());

    histo1D["err2Down"] = (TH1F*)shapefile->Get((sysname + "PUDown").c_str());
    histo1D["err3Down"] = (TH1F*)shapefile->Get((sysname + "TTJets_HDAMPDown").c_str());
    histo1D["err4Down"] = (TH1F*)shapefile->Get((sysname + "heavyFlavDown").c_str());
    histo1D["err5Down"] = (TH1F*)shapefile->Get((sysname + "JERDown").c_str());
    histo1D["err6Down"] = (TH1F*)shapefile->Get((sysname + "JESDown").c_str());
    histo1D["err7Down"] = (TH1F*)shapefile->Get((sysname + "TTUEDown").c_str());
    histo1D["err8Down"] = (TH1F*)shapefile->Get((sysname + "TTISRDown").c_str());
    histo1D["err9Down"] = (TH1F*)shapefile->Get((sysname + "TTFSRDown").c_str());
    histo1D["err10Down"] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVLFDown").c_str());
    histo1D["err11Down"] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVHFDown").c_str());
    histo1D["err12Down"] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVHFStats1Down").c_str());
    histo1D["err13Down"] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVHFStats2Down").c_str());
    histo1D["err14Down"] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVLFStats1Down").c_str());
    histo1D["err15Down"] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVLFStats2Down").c_str());
    histo1D["err16Down"] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVCFErr1Down").c_str());
    histo1D["err17Down"] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVCFErr2Down").c_str());

    histo1D["main_ttbar"] = (TH1F*)shapefile->Get((sysname + "nominal").c_str());

    for(int binN = 1; binN < nBins + 1; ++binN) {
        float binContentMax = -1, binContentMin = 1000000000000000;

        for(int weightIt = 1; weightIt < 9; ++weightIt) {
            if(weightIt == 6 || weightIt == 8) {
                continue;
            }
            string weightStr = static_cast<ostringstream*>(&(ostringstream() << weightIt))->str();
            string weightHistoName = ("weight" + weightStr).c_str();
            if(binContentMin > histo1D[weightHistoName]->GetBinContent(binN))
                binContentMin = histo1D[weightHistoName]->GetBinContent(binN);
            if(binContentMax < histo1D[weightHistoName]->GetBinContent(binN))
                binContentMax = histo1D[weightHistoName]->GetBinContent(binN);
        }

        float err1up, err2up, err3up, err4up, err5up, err6up, err7up, err8up, err9up, err10up, err11up, err12up, err13up, err14up, err15up, err16up, err17up;
        float err1down, err2down, err3down, err4down, err5down, err6down, err7down, err8down, err9down, err10down, err11down, err12down, err13down, err14down, err15down, err16down, err17down;

        err1up = binContentMax - histo1D["main_ttbar"]->GetBinContent(binN);
        err2up = histo1D["err2Up"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err3up = histo1D["err3Up"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err4up = histo1D["err4Up"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err5up = histo1D["err5Up"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err6up = histo1D["err6Up"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err7up = histo1D["err7Up"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err8up = histo1D["err8Up"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err9up = histo1D["err9Up"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err10up = histo1D["err10Up"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err11up = histo1D["err11Up"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err12up = histo1D["err12Up"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err13up = histo1D["err13Up"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err14up = histo1D["err14Up"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err15up = histo1D["err15Up"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err16up = histo1D["err16Up"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err17up = histo1D["err17Up"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);

        err1down = histo1D["main_ttbar"]->GetBinContent(binN) - binContentMin;
        err2down = histo1D["err2Down"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err3down = histo1D["err3Down"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err4down = histo1D["err4Down"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err5down = histo1D["err5Down"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err6down = histo1D["err6Down"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err7down = histo1D["err7Down"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err8down = histo1D["err8Down"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err9down = histo1D["err9Down"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err10down = histo1D["err10Down"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err11down = histo1D["err11Down"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err12down = histo1D["err12Down"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err13down = histo1D["err13Down"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err14down = histo1D["err14Down"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err15down = histo1D["err15Down"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err16down = histo1D["err16Down"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);
        err17down = histo1D["err17Down"]->GetBinContent(binN) - histo1D["main_ttbar"]->GetBinContent(binN);

        float errorbandUp = sqrt(err1up*err1up+err2up*err2up+err3up*err3up+err4up*err4up+err5up*err5up+err6up*err6up+err7up*err7up+err8up*err8up+err9up*err9up+err10up*err10up+err11up*err11up+err12up*err12up+err13up*err13up+err14up*err14up+err15up*err15up+err16up*err16up+err17up*err17up);
        float errorbandDown = sqrt(err1down*err1down+err2down*err2down+err3down*err3down+err4down*err4down+err5down*err5down+err6down*err6down+err7down*err7down+err8down*err8down+err9down*err9down+err10down*err10down+err11down*err11down+err12down*err12down+err13down*err13down+err14down*err14down+err15down*err15down+err16down*err16down+err17down*err17down);

        histo1D["weightPlus"]->SetBinContent(binN, histo1D["main_ttbar"]->GetBinContent(binN) + err1up);
        histo1D["weightMinus"]->SetBinContent(binN, histo1D["main_ttbar"]->GetBinContent(binN) - err1down);
    }

    errorfile->cd();
    errorfile->cd(("MultiSamplePlot_" + sVarofinterest).c_str());
    histo1D["weightMinus"]->Write("Minus");
    histo1D["weightPlus"]->Write("Plus");
    histo1D["weight0"]->Write("Nominal");
    cout << "wrote weights in errorfile" << endl;
}

void GetScaleEnvelope(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string xmlNom,
    string CraneenPath,
    string shapefileName,
    string mainTTbarSample)
{

    cout << "Producing envelope for tt MEScale uncertainty" << endl;
    histo1D["weightPlus"] = new TH1F("Plus", "Plus", nBins, plotLow, plotHigh);
    histo1D["weightMinus"] = new TH1F("Minus", "Minus", nBins, plotLow, plotHigh);

    // TFile * reopenSF = new TFile(shapefileName.c_str());
    histo1D["weight0"] = (TH1F*)shapefile->Get("Genweight_tt");
    histo1D["weight1"] = (TH1F*)shapefile->Get("weight1_tt");
    histo1D["weight2"] = (TH1F*)shapefile->Get("weight2_tt");
    histo1D["weight3"] = (TH1F*)shapefile->Get("weight3_tt");
    histo1D["weight4"] = (TH1F*)shapefile->Get("weight4_tt");
    histo1D["weight5"] = (TH1F*)shapefile->Get("weight5_tt");
    histo1D["weight6"] = (TH1F*)shapefile->Get("weight6_tt");
    histo1D["weight7"] = (TH1F*)shapefile->Get("weight7_tt");
    histo1D["weight8"] = (TH1F*)shapefile->Get("weight8_tt");

    // float weighty = weight0->Integral(); cout<<weighty<<endl;

    cout << "Got weights" << endl;

    for(int binN = 1; binN < nBins + 1; ++binN) {
        float binContentMax = -1, binContentMin = 1000000000000000;

        for(int weightIt = 1; weightIt < 9; ++weightIt) {
            if(weightIt == 6 || weightIt == 8) {
                continue; // extreme weights with 1/2u and 2u
            }

            string weightStr = static_cast<ostringstream*>(&(ostringstream() << weightIt))->str();
            string weightHistoName = ("weight" + weightStr).c_str();
            //cout << "Bin " << binN << ", weight " << weightIt << " : " << histo1D[weightHistoName]->GetBinContent(binN) << endl;
            if(binContentMin > histo1D[weightHistoName]->GetBinContent(binN))
                binContentMin = histo1D[weightHistoName]->GetBinContent(binN);
            if(binContentMax < histo1D[weightHistoName]->GetBinContent(binN))
                binContentMax = histo1D[weightHistoName]->GetBinContent(binN);
        }
        //cout << "Setting bin " << binN << " content: " << binContentMin << ", " << binContentMax << endl;
        histo1D["weightPlus"]->SetBinContent(binN, binContentMax);
        histo1D["weightMinus"]->SetBinContent(binN, binContentMin);
    }
    /*
    errorfile->cd();
    errorfile->cd(("MultiSamplePlot_" + sVarofinterest).c_str());
    histo1D["weightMinus"]->Write("Minus");
    histo1D["weightPlus"]->Write("Plus");
    histo1D["weight0"]->Write("Nominal");
    cout << "wrote weights in errorfile" << endl;
    */
    shapefile->cd();
    string MEScalesysname = channel + "__" + "ttbarTTX" + "__ttMEScale";
    histo1D["weightMinus"]->Write((MEScalesysname + "Down").c_str());
    histo1D["weightPlus"]->Write((MEScalesysname + "Up").c_str());
    cout << "wrote sys MEScale shapes in shapefile" << endl;
}

void GetScaleEnvelope_tttt(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string xmlNom,
    string CraneenPath,
    string shapefileName,
    string mainTTbarSample)
{

    cout << "Producing envelope for tttt MEScale uncertainty" << endl;
    histo1D["weightPlus_tttt"] = new TH1F("Plus_tttt", "Plus_tttt", nBins, plotLow, plotHigh);
    histo1D["weightMinus_tttt"] = new TH1F("Minus_tttt", "Minus_tttt", nBins, plotLow, plotHigh);

    // TFile * reopenSF = new TFile(shapefileName.c_str());
    histo1D["weight_tttt0"] = (TH1F*)shapefile->Get("Genweight_tttt");
    histo1D["weight_tttt1"] = (TH1F*)shapefile->Get("weight1_tttt");
    histo1D["weight_tttt2"] = (TH1F*)shapefile->Get("weight2_tttt");
    histo1D["weight_tttt3"] = (TH1F*)shapefile->Get("weight3_tttt");
    histo1D["weight_tttt4"] = (TH1F*)shapefile->Get("weight4_tttt");
    histo1D["weight_tttt5"] = (TH1F*)shapefile->Get("weight5_tttt");
    histo1D["weight_tttt6"] = (TH1F*)shapefile->Get("weight6_tttt");
    histo1D["weight_tttt7"] = (TH1F*)shapefile->Get("weight7_tttt");
    histo1D["weight_tttt8"] = (TH1F*)shapefile->Get("weight8_tttt");
    /*
    cout << histo1D["weight_tttt1"]->GetMaximum() << endl;
    cout << histo1D["weight1_tttt"]->GetMaximum() << endl;
    cout << histo1D["weight_tttt2"]->GetMaximum() << endl;
    cout << histo1D["weight_tttt3"]->GetMaximum() << endl;
    cout << histo1D["weight_tttt4"]->GetMaximum() << endl;
    cout << histo1D["weight_tttt5"]->GetMaximum() << endl;
    cout << histo1D["weight_tttt7"]->GetMaximum() << endl;
    */
    cout << "Got weights" << endl;

    for(int binN = 1; binN < nBins + 1; ++binN) {
        float binContentMax = -1, binContentMin = 1000000000000000;

        for(int weightIt = 1; weightIt < 9; ++weightIt) {
            if(weightIt == 6 || weightIt == 8) {
                continue; // extreme weights with 1/2u and 2u
            }

            string weightStr = static_cast<ostringstream*>(&(ostringstream() << weightIt))->str();
            string weightHistoName = ("weight_tttt" + weightStr).c_str();
            //cout << "Bin " << binN << ", weight " << weightIt << " : " << histo1D[weightHistoName]->GetBinContent(binN) << endl;
            if(binContentMin > histo1D[weightHistoName]->GetBinContent(binN))
                binContentMin = histo1D[weightHistoName]->GetBinContent(binN);
            if(binContentMax < histo1D[weightHistoName]->GetBinContent(binN))
                binContentMax = histo1D[weightHistoName]->GetBinContent(binN);
        }
        //cout << "Setting bin " << binN << " content: " << binContentMin << ", " << binContentMax << endl;
        histo1D["weightPlus_tttt"]->SetBinContent(binN, binContentMax);
        histo1D["weightMinus_tttt"]->SetBinContent(binN, binContentMin);
    }

    shapefile->cd();
    string MEScalesysname = channel + "__" + "NP_overlay_ttttNLO" + "__ttttMEScale";
    histo1D["weightMinus_tttt"]->Write((MEScalesysname + "Down").c_str());
    histo1D["weightPlus_tttt"]->Write((MEScalesysname + "Up").c_str());
    cout << "wrote sys MEScale shapes in shapefile" << endl;
}

void GetMatching(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string xmlNom,
    string CraneenPath,
    string mainTTbarSample,
    string otherTTbarsample)
{

    cout << "Producing envelope for ttGenerator uncertainty" << endl;
    histo1D["ttGeneratorPlus"] = new TH1F("Plus_match", "Plus", nBins, plotLow, plotHigh);
    histo1D["ttGeneratorMinus"] = new TH1F("Minus_match", "Minus", nBins, plotLow, plotHigh);

    histo1D["main_ttbar"] = (TH1F*)shapefile->Get((channel + "__" + mainTTbarSample + "__nominal").c_str());
    histo1D["other_ttbar"] = (TH1F*)shapefile->Get((channel + "__" + otherTTbarsample + "__nominal").c_str());
    cout << "Got ttGenerator histos" << endl;

    for(int binN = 1; binN < nBins + 1; ++binN) {
        float binContentMax = -1, binContentMin = 1000000000000000;
        float errorMatching = abs(histo1D["main_ttbar"]->GetBinContent(binN) - histo1D["other_ttbar"]->GetBinContent(binN));

        histo1D["ttGeneratorPlus"]->SetBinContent(binN, histo1D["main_ttbar"]->GetBinContent(binN) + errorMatching);
        histo1D["ttGeneratorMinus"]->SetBinContent(binN, histo1D["main_ttbar"]->GetBinContent(binN) - errorMatching);
    }

    shapefile->cd();
    string ttGeneratorsysname = channel + "__" + mainTTbarSample + "__ttGenerator";
    histo1D["ttGeneratorMinus"]->Write((ttGeneratorsysname + "Down").c_str());
    histo1D["ttGeneratorPlus"]->Write((ttGeneratorsysname + "Up").c_str());
    cout << "wrote sys ttGenerator shapes in shapefile" << endl;
}

void GetMatchingSplit(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string xmlNom,
    string CraneenPath,
    string mainTTbarSample,
    string otherTTbarsample,
    string sSplitVar,
    float fbSplit,
    float ftSplit,
    float fwSplit)
{
    string plotname; ///// Jet Split plot
    string numStr;
    string sbSplit = static_cast<ostringstream*>(&(ostringstream() << fbSplit))->str();
    string stSplit = static_cast<ostringstream*>(&(ostringstream() << ftSplit))->str();
    string swSplit = static_cast<ostringstream*>(&(ostringstream() << fwSplit))->str();
    cout << "Producing envelope for ttGenerator uncertainty" << endl;
    for(int s = fbSplit; s <= ftSplit; s += fwSplit) {
        numStr = static_cast<ostringstream*>(&(ostringstream() << s))->str();

        histo1D[("ttGeneratorPlus"+numStr).c_str()] = new TH1F(("Plus_match"+numStr).c_str(), "Plus", nBins, plotLow, plotHigh);
        histo1D[("ttGeneratorMinus"+numStr).c_str()] = new TH1F(("Minus_match"+numStr).c_str(), "Minus", nBins, plotLow, plotHigh);

        histo1D["main_ttbar"] = (TH1F*)shapefile->Get((channel + numStr + sSplitVar + "__" + mainTTbarSample + "__nominal").c_str());
        histo1D["other_ttbar"] = (TH1F*)shapefile->Get((channel + numStr + sSplitVar + "__" + otherTTbarsample + "__nominal").c_str());
        cout << "Got ttGenerator histos" << endl;
        cout << channel + numStr + sSplitVar + "__" + mainTTbarSample + "__nominal" << "    " << channel + numStr + sSplitVar + "__" + otherTTbarsample + "__nominal" << endl;
        for(int binN = 1; binN < nBins + 1; ++binN) {
            float binContentMax = -1, binContentMin = 1000000000000000;
            float errorMatching = abs(histo1D["main_ttbar"]->GetBinContent(binN) - histo1D["other_ttbar"]->GetBinContent(binN));

            histo1D[("ttGeneratorPlus"+numStr).c_str()]->SetBinContent(binN, histo1D["main_ttbar"]->GetBinContent(binN) + errorMatching);
            histo1D[("ttGeneratorMinus"+numStr).c_str()]->SetBinContent(binN, histo1D["main_ttbar"]->GetBinContent(binN) - errorMatching);
        }

        shapefile->cd();
        string ttGeneratorsysname = channel + numStr + sSplitVar + "__" + mainTTbarSample + "__ttGenerator";
        histo1D[("ttGeneratorMinus"+numStr).c_str()]->Write((ttGeneratorsysname + "Down").c_str());
        histo1D[("ttGeneratorPlus"+numStr).c_str()]->Write((ttGeneratorsysname + "Up").c_str());
        cout << "wrote sys ttGenerator shapes in shapefile" << endl;
    }
}

void GetScaleEnvelopeSplit(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string sSplitVar,
    float fbSplit,
    float ftSplit,
    float fwSplit,
    string xmlNom,
    string CraneenPath,
    string shapefileName,
    string mainTTbarSample)
{
    string plotname; ///// Jet Split plot
    string numStr;
    string sbSplit = static_cast<ostringstream*>(&(ostringstream() << fbSplit))->str();
    string stSplit = static_cast<ostringstream*>(&(ostringstream() << ftSplit))->str();
    string swSplit = static_cast<ostringstream*>(&(ostringstream() << fwSplit))->str();

    cout << "Producing envelope for tt MEScale uncertainty" << endl;
    for(int s = fbSplit; s <= ftSplit; s += fwSplit) {
        numStr = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        histo1D[("weightPlus" + numStr).c_str()] = new TH1F(("Plus_tt"+numStr).c_str(), "Plus", nBins, plotLow, plotHigh);
        histo1D[("weightMinus" + numStr).c_str()] = new TH1F(("Minus_tt"+numStr).c_str(), "Minus", nBins, plotLow, plotHigh);

        // TFile * reopenSF = new TFile(shapefileName.c_str());
        histo1D[("weight0_tt" + numStr).c_str()] = (TH1F*)shapefile->Get(("Genweight_tt" + numStr).c_str());
        histo1D[("weight1_tt" + numStr).c_str()] = (TH1F*)shapefile->Get(("weight1_tt" + numStr).c_str());
        histo1D[("weight2_tt" + numStr).c_str()] = (TH1F*)shapefile->Get(("weight2_tt" + numStr).c_str());
        histo1D[("weight3_tt" + numStr).c_str()] = (TH1F*)shapefile->Get(("weight3_tt" + numStr).c_str());
        histo1D[("weight4_tt" + numStr).c_str()] = (TH1F*)shapefile->Get(("weight4_tt" + numStr).c_str());
        histo1D[("weight5_tt" + numStr).c_str()] = (TH1F*)shapefile->Get(("weight5_tt" + numStr).c_str());
        histo1D[("weight6_tt" + numStr).c_str()] = (TH1F*)shapefile->Get(("weight6_tt" + numStr).c_str());
        histo1D[("weight7_tt" + numStr).c_str()] = (TH1F*)shapefile->Get(("weight7_tt" + numStr).c_str());
        histo1D[("weight8_tt" + numStr).c_str()] = (TH1F*)shapefile->Get(("weight8_tt" + numStr).c_str());

        cout << "Got weights" << endl;

        for(int binN = 1; binN < nBins + 1; ++binN) {
            float binContentMax = -1, binContentMin = 1000000000000000;

            for(int weightIt = 1; weightIt < 9; ++weightIt) {
                if(weightIt == 6 || weightIt == 8) {
                    continue; // extreme weights with 1/2u and 2u
                }

                string weightStr = static_cast<ostringstream*>(&(ostringstream() << weightIt))->str();
                string weightHistoName = ("weight" + weightStr + "_tt" + numStr).c_str();
                // cout << weightHistoName << endl;
                if(binContentMin > histo1D[weightHistoName]->GetBinContent(binN))
                    binContentMin = histo1D[weightHistoName]->GetBinContent(binN);
                if(binContentMax < histo1D[weightHistoName]->GetBinContent(binN))
                    binContentMax = histo1D[weightHistoName]->GetBinContent(binN);
                // cout << "binContentMax: " << binContentMax << "binContentMin: " << binContentMin << endl;
                // cout<<"bin number : "<<binN<<"   bincontent: "<<histo1D["weight0"]->GetBinContent(binN)<<endl;
            }
            histo1D[("weightPlus" + numStr).c_str()]->SetBinContent(binN, binContentMax);
            histo1D[("weightMinus" + numStr).c_str()]->SetBinContent(binN, binContentMin);
        }

        errorfile->cd();
        errorfile->mkdir(("MultiSamplePlot_" + sVarofinterest + numStr + sSplitVar).c_str());
        errorfile->cd(("MultiSamplePlot_" + sVarofinterest + numStr + sSplitVar).c_str());
        histo1D[("weightMinus" + numStr).c_str()]->Write("Minus");
        histo1D[("weightPlus" + numStr).c_str()]->Write("Plus");
        histo1D[("weight0_tt" + numStr).c_str()]->Write("Nominal");
        cout << "wrote weights in errorfile" << endl;
        shapefile->cd();
        string MEScalesysname = channel + numStr + sSplitVar + "__TTJetsPowheg__ttMEScale";
        cout << MEScalesysname << endl;
        histo1D[("weightMinus" + numStr).c_str()]->Write((MEScalesysname + "Down").c_str());
        histo1D[("weightPlus" + numStr).c_str()]->Write((MEScalesysname + "Up").c_str());
        cout << "wrote sys MEScale shapes in shapefile" << endl;
    }
}

void GetScaleEnvelopeSplit_tttt(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string sSplitVar,
    float fbSplit,
    float ftSplit,
    float fwSplit,
    string xmlNom,
    string CraneenPath,
    string shapefileName,
    string mainTTbarSample)
{
    string plotname; ///// Jet Split plot
    string numStr;
    string sbSplit = static_cast<ostringstream*>(&(ostringstream() << fbSplit))->str();
    string stSplit = static_cast<ostringstream*>(&(ostringstream() << ftSplit))->str();
    string swSplit = static_cast<ostringstream*>(&(ostringstream() << fwSplit))->str();

    cout << "Producing envelope for tttt MEScale uncertainty" << endl;
    for(int s = fbSplit; s <= ftSplit; s += fwSplit) {
        numStr = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        histo1D[("weightPlus_tttt" + numStr).c_str()] = new TH1F(("Plus_tttt"+numStr).c_str(), "Plus_tttt", nBins, plotLow, plotHigh);
        histo1D[("weightMinus_tttt" + numStr).c_str()] = new TH1F(("Minus_tttt"+numStr).c_str(), "Minus_tttt", nBins, plotLow, plotHigh);

        // TFile * reopenSF = new TFile(shapefileName.c_str());
        histo1D[("weight0_tttt" + numStr).c_str()] = (TH1F*)shapefile->Get(("Genweight_tttt" + numStr).c_str());
        histo1D[("weight1_tttt" + numStr).c_str()] = (TH1F*)shapefile->Get(("weight1_tttt" + numStr).c_str());
        histo1D[("weight2_tttt" + numStr).c_str()] = (TH1F*)shapefile->Get(("weight2_tttt" + numStr).c_str());
        histo1D[("weight3_tttt" + numStr).c_str()] = (TH1F*)shapefile->Get(("weight3_tttt" + numStr).c_str());
        histo1D[("weight4_tttt" + numStr).c_str()] = (TH1F*)shapefile->Get(("weight4_tttt" + numStr).c_str());
        histo1D[("weight5_tttt" + numStr).c_str()] = (TH1F*)shapefile->Get(("weight5_tttt" + numStr).c_str());
        histo1D[("weight6_tttt" + numStr).c_str()] = (TH1F*)shapefile->Get(("weight6_tttt" + numStr).c_str());
        histo1D[("weight7_tttt" + numStr).c_str()] = (TH1F*)shapefile->Get(("weight7_tttt" + numStr).c_str());
        histo1D[("weight8_tttt" + numStr).c_str()] = (TH1F*)shapefile->Get(("weight8_tttt" + numStr).c_str());

        cout << "Got weights" << endl;

        for(int binN = 1; binN < nBins + 1; ++binN) {
            float binContentMax = -1, binContentMin = 1000000000000000;

            for(int weightIt = 1; weightIt < 9; ++weightIt) {
                if(weightIt == 6 || weightIt == 8) {
                    continue; // extreme weights with 1/2u and 2u
                }

                string weightStr = static_cast<ostringstream*>(&(ostringstream() << weightIt))->str();
                string weightHistoName = ("weight" + weightStr + "_tttt" + numStr).c_str();
                // cout << weightHistoName << endl;
                if(binContentMin > histo1D[weightHistoName]->GetBinContent(binN))
                    binContentMin = histo1D[weightHistoName]->GetBinContent(binN);
                if(binContentMax < histo1D[weightHistoName]->GetBinContent(binN))
                    binContentMax = histo1D[weightHistoName]->GetBinContent(binN);
                // cout << "binContentMax: " << binContentMax << "binContentMin: " << binContentMin << endl;
                // cout<<"bin number : "<<binN<<"   bincontent: "<<histo1D["weight0"]->GetBinContent(binN)<<endl;
            }
            histo1D[("weightPlus_tttt" + numStr).c_str()]->SetBinContent(binN, binContentMax);
            histo1D[("weightMinus_tttt" + numStr).c_str()]->SetBinContent(binN, binContentMin);
        }

        // errorfile->cd();
        // errorfile->mkdir(("MultiSamplePlot_" + sVarofinterest + numStr + sSplitVar).c_str());
        // errorfile->cd(("MultiSamplePlot_" + sVarofinterest + numStr + sSplitVar).c_str());
        // histo1D[("weightMinus_tttt" + numStr).c_str()]->Write("Minus");
        // histo1D[("weightPlus_tttt" + numStr).c_str()]->Write("Plus");
        // histo1D[("weight0_tttt" + numStr).c_str()]->Write("Nominal");
        // cout << "wrote weights in errorfile" << endl;
        shapefile->cd();
        string MEScalesysname = channel + numStr + sSplitVar + "__" + "NP_overlay_ttttNLO" + "__ttttMEScale";
        // cout << MEScalesysname << endl;
        histo1D[("weightMinus_tttt" + numStr).c_str()]->Write((MEScalesysname + "Down").c_str());
        histo1D[("weightPlus_tttt" + numStr).c_str()]->Write((MEScalesysname + "Up").c_str());
        cout << "wrote sys MEScale shapes in shapefile" << endl;
    }
}

void GetScaleEnvelopeSplit2_tttt(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string sSplitVar1,
    float fbSplit1,
    float ftSplit1,
    float fwSplit1,
    string sSplitVar2,
    float fbSplit2,
    float ftSplit2,
    float fwSplit2,
    string xmlNom,
    string CraneenPath,
    string shapefileName,
    string mainTTbarSample)
{
    string plotname; ///// Jet Split plot
    string numStr1;
    string numStr2;
    string sbSplit1 = static_cast<ostringstream*>(&(ostringstream() << fbSplit1))->str();
    string stSplit1 = static_cast<ostringstream*>(&(ostringstream() << ftSplit1))->str();
    string swSplit1 = static_cast<ostringstream*>(&(ostringstream() << fwSplit1))->str();
    string sbSplit2 = static_cast<ostringstream*>(&(ostringstream() << fbSplit2))->str();
    string stSplit2 = static_cast<ostringstream*>(&(ostringstream() << ftSplit2))->str();
    string swSplit2 = static_cast<ostringstream*>(&(ostringstream() << fwSplit2))->str();

    cout << "Producing envelope for tttt MEScale uncertainty" << endl;

    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        for(int t2 = fbSplit2; t2 <= ftSplit2; t2 += fwSplit2) {
            numStr2 = static_cast<ostringstream*>(&(ostringstream() << t2))->str();
            // cout << numStr1 + sSplitVar1 + numStr2 + sSplitVar2 << endl;
            histo1D[("weightPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                new TH1F(("Plus_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "Plus_tttt", nBins, plotLow, plotHigh);
            histo1D[("weightMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                new TH1F(("Minus_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "Minus_tttt", nBins, plotLow, plotHigh);

            // TFile * reopenSF = new TFile(shapefileName.c_str());
            histo1D[("weight0_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("Genweight_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight1_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight1_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight2_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight2_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight3_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight3_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight4_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight4_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight5_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight5_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight6_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight6_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight7_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight7_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight8_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight8_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());

            cout << "Got weights" << endl;

            for(int binN = 1; binN < nBins + 1; ++binN) {
                float binContentMax = -1, binContentMin = 1000000000000000;

                for(int weightIt = 1; weightIt < 9; ++weightIt) {
                    if(weightIt == 6 || weightIt == 8) {
                        continue; // extreme weights with 1/2u and 2u
                    }

                    string weightStr = static_cast<ostringstream*>(&(ostringstream() << weightIt))->str();
                    string weightHistoName =
                        ("weight" + weightStr + "_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str();
                    // cout << weightHistoName << endl;
                    if(binContentMin > histo1D[weightHistoName]->GetBinContent(binN))
                        binContentMin = histo1D[weightHistoName]->GetBinContent(binN);
                    if(binContentMax < histo1D[weightHistoName]->GetBinContent(binN))
                        binContentMax = histo1D[weightHistoName]->GetBinContent(binN);
                    // cout << "binContentMax: " << binContentMax << "binContentMin: " << binContentMin << endl;
                    // cout<<"bin number : "<<binN<<"   bincontent: "<<histo1D["weight0"]->GetBinContent(binN)<<endl;
                }
                histo1D[("weightPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->SetBinContent(binN, binContentMax);
                histo1D[("weightMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->SetBinContent(binN, binContentMin);
            }

            shapefile->cd();
            string MEScalesysname = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__TTTTMEScale";
            // cout << MEScalesysname << endl;
            histo1D[("weightMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "Down").c_str());
            histo1D[("weightPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "Up").c_str());
            cout << "wrote sys MEScale shapes in shapefile" << endl;
        }
    }
}

void GetErrorBandSplit2(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string sSplitVar1,
    float fbSplit1,
    float ftSplit1,
    float fwSplit1,
    string sSplitVar2,
    float fbSplit2,
    float ftSplit2,
    float fwSplit2,
    string xmlNom,
    string CraneenPath,
    string shapefileName,
    string mainTTbarSample)
{
    string plotname; ///// Jet Split plot
    string numStr1;
    string numStr2;
    string sbSplit1 = static_cast<ostringstream*>(&(ostringstream() << fbSplit1))->str();
    string stSplit1 = static_cast<ostringstream*>(&(ostringstream() << ftSplit1))->str();
    string swSplit1 = static_cast<ostringstream*>(&(ostringstream() << fwSplit1))->str();
    string sbSplit2 = static_cast<ostringstream*>(&(ostringstream() << fbSplit2))->str();
    string stSplit2 = static_cast<ostringstream*>(&(ostringstream() << ftSplit2))->str();
    string swSplit2 = static_cast<ostringstream*>(&(ostringstream() << fwSplit2))->str();

    cout << "Producing Error Band for ttbar" << endl;

    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        for(int t2 = fbSplit2; t2 <= ftSplit2; t2 += fwSplit2) {
            numStr2 = static_cast<ostringstream*>(&(ostringstream() << t2))->str();
            histo1D[("weightPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                new TH1F(("Plus_err" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "Plus", nBins, plotLow, plotHigh);
            histo1D[("weightMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                new TH1F(("Minus_err" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "Minus", nBins, plotLow, plotHigh);

            string sysname = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__ttbarTTX__";

            histo1D[("weight0_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("Genweight_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight1_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight1_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight2_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight2_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight3_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight3_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight4_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight4_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight5_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight5_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight6_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight6_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight7_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight7_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight8_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight8_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());

            histo1D[("err2Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "PUUp").c_str());
            histo1D[("err3Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "TTJets_HDAMPUp").c_str());
            histo1D[("err4Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "heavyFlavUp").c_str());
            histo1D[("err5Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "JERUp").c_str());
            histo1D[("err6Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "JESUp").c_str());
            histo1D[("err7Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "TTUEUp").c_str());
            histo1D[("err8Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "TTISRUp").c_str());
            histo1D[("err9Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "TTFSRUp").c_str());
            histo1D[("err10Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVLFUp").c_str());
            histo1D[("err11Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVHFUp").c_str());
            histo1D[("err12Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVHFStats1Up").c_str());
            histo1D[("err13Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVHFStats2Up").c_str());
            histo1D[("err14Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVLFStats1Up").c_str());
            histo1D[("err15Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVLFStats2Up").c_str());
            histo1D[("err16Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVCFErr1Up").c_str());
            histo1D[("err17Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVCFErr2Up").c_str());

            histo1D[("err2Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "PUDown").c_str());
            histo1D[("err3Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "TTJets_HDAMPDown").c_str());
            histo1D[("err4Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "heavyFlavDown").c_str());
            histo1D[("err5Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "JERDown").c_str());
            histo1D[("err6Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "JESDown").c_str());
            histo1D[("err7Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "TTUEDown").c_str());
            histo1D[("err8Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "TTISRDown").c_str());
            histo1D[("err9Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "TTFSRDown").c_str());
            histo1D[("err10Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVLFDown").c_str());
            histo1D[("err11Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVHFDown").c_str());
            histo1D[("err12Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVHFStats1Down").c_str());
            histo1D[("err13Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVHFStats2Down").c_str());
            histo1D[("err14Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVLFStats1Down").c_str());
            histo1D[("err15Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVLFStats2Down").c_str());
            histo1D[("err16Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVCFErr1Down").c_str());
            histo1D[("err17Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "btagWeightCSVCFErr2Down").c_str());

            histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = (TH1F*)shapefile->Get((sysname + "nominal").c_str());

            for(int binN = 1; binN < nBins + 1; ++binN) {
                float binContentMax = -1, binContentMin = 1000000000000000;

                for(int weightIt = 1; weightIt < 9; ++weightIt) {
                    if(weightIt == 6 || weightIt == 8) {
                        continue; // extreme weights with 1/2u and 2u
                    }

                    string weightStr = static_cast<ostringstream*>(&(ostringstream() << weightIt))->str();
                    string weightHistoName =
                        ("weight" + weightStr + "_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str();
                    if(binContentMin > histo1D[weightHistoName]->GetBinContent(binN))
                        binContentMin = histo1D[weightHistoName]->GetBinContent(binN);
                    if(binContentMax < histo1D[weightHistoName]->GetBinContent(binN))
                        binContentMax = histo1D[weightHistoName]->GetBinContent(binN);
                }

                float err1up, err2up, err3up, err4up, err5up, err6up, err7up, err8up, err9up, err10up, err11up, err12up, err13up, err14up, err15up, err16up, err17up;
                float err1down, err2down, err3down, err4down, err5down, err6down, err7down, err8down, err9down, err10down, err11down, err12down, err13down, err14down,
                      err15down, err16down, err17down;

                err1up = binContentMax - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err2up = histo1D[("err2Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN)
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err3up = histo1D[("err3Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN) 
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err4up = histo1D[("err4Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN) 
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err5up = histo1D[("err5Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN) 
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err6up = histo1D[("err6Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN) 
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err7up = histo1D[("err7Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN) 
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err8up = histo1D[("err8Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN) 
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err9up = histo1D[("err9Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN) 
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err10up = histo1D[("err10Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN) 
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err11up = histo1D[("err11Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN) 
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err12up = histo1D[("err12Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN) 
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err13up = histo1D[("err13Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN) 
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err14up = histo1D[("err14Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN) 
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err15up = histo1D[("err15Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN) 
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err16up = histo1D[("err16Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN) 
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err17up = histo1D[("err17Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN) 
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);

                err1down = binContentMin - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err2down = histo1D[("err2Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN) 
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err3down = histo1D[("err3Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN)
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err4down = histo1D[("err4Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN)
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err5down = histo1D[("err5Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN)
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err6down = histo1D[("err6Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN)
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err7down = histo1D[("err7Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN)
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err8down = histo1D[("err8Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN)
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err9down = histo1D[("err9Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN)
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err10down = histo1D[("err10Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN)
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err11down = histo1D[("err11Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN)
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err12down = histo1D[("err12Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN)
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err13down = histo1D[("err13Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN)
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err14down = histo1D[("err14Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN)
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err15down = histo1D[("err15Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN)
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err16down = histo1D[("err16Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN)
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);
                err17down = histo1D[("err17Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN)
                         - histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN);

                float errorbandUp = sqrt(err1up*err1up+err2up*err2up+err3up*err3up+err4up*err4up+err5up*err5up+err6up*err6up+
                                         err7up*err7up+err8up*err8up+err9up*err9up+err10up*err10up+err11up*err11up+err12up*err12up+
                                         err13up*err13up+err14up*err14up+err15up*err15up+err16up*err16up+err17up*err17up);
                float errorbandDown = sqrt(err1down*err1down+err2down*err2down+err3down*err3down+err4down*err4down+err5down*err5down+
                                           err6down*err6down+err7down*err7down+err8down*err8down+err9down*err9down+err10down*err10down+
                                           err11down*err11down+err12down*err12down+err13down*err13down+err14down*err14down+err15down*err15down+
                                           err16down*err16down+err17down*err17down);
                histo1D[("weightPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->SetBinContent(binN, 
				histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN) + errorbandUp);
                histo1D[("weightMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->SetBinContent(binN,
				histo1D[("main_ttbar" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->GetBinContent(binN) - errorbandDown);
            }
            errorfile->cd();
            errorfile->mkdir(("MultiSamplePlot_" + sVarofinterest + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            errorfile->cd(("MultiSamplePlot_" + sVarofinterest + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weightMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write("Minus");
            histo1D[("weightPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write("Plus");
            histo1D[("weight0_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write("Nominal");
        }
    }
}


void GetScaleEnvelopeSplit2(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string sSplitVar1,
    float fbSplit1,
    float ftSplit1,
    float fwSplit1,
    string sSplitVar2,
    float fbSplit2,
    float ftSplit2,
    float fwSplit2,
    string xmlNom,
    string CraneenPath,
    string shapefileName,
    string mainTTbarSample)
{
    string plotname; ///// Jet Split plot
    string numStr1;
    string numStr2;
    string sbSplit1 = static_cast<ostringstream*>(&(ostringstream() << fbSplit1))->str();
    string stSplit1 = static_cast<ostringstream*>(&(ostringstream() << ftSplit1))->str();
    string swSplit1 = static_cast<ostringstream*>(&(ostringstream() << fwSplit1))->str();
    string sbSplit2 = static_cast<ostringstream*>(&(ostringstream() << fbSplit2))->str();
    string stSplit2 = static_cast<ostringstream*>(&(ostringstream() << ftSplit2))->str();
    string swSplit2 = static_cast<ostringstream*>(&(ostringstream() << fwSplit2))->str();

    cout << "Producing envelope for tt MEScale uncertainty" << endl;

    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        for(int t2 = fbSplit2; t2 <= ftSplit2; t2 += fwSplit2) {
            numStr2 = static_cast<ostringstream*>(&(ostringstream() << t2))->str();
            // cout << numStr1 + sSplitVar1 + numStr2 + sSplitVar2 << endl;
            histo1D[("weightPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                new TH1F(("Plus_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "Plus", nBins, plotLow, plotHigh);
            histo1D[("weightMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                new TH1F(("Minus_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "Minus", nBins, plotLow, plotHigh);

            // TFile * reopenSF = new TFile(shapefileName.c_str());
            histo1D[("weight0_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("Genweight_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight1_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight1_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight2_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight2_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight3_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight3_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight4_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight4_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight5_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight5_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight6_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight6_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight7_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight7_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight8_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("weight8_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());

            cout << "Got weights" << endl;

            for(int binN = 1; binN < nBins + 1; ++binN) {
                float binContentMax = -1, binContentMin = 1000000000000000;

                for(int weightIt = 1; weightIt < 9; ++weightIt) {
                    if(weightIt == 6 || weightIt == 8) {
                        continue; // extreme weights with 1/2u and 2u
                    }

                    string weightStr = static_cast<ostringstream*>(&(ostringstream() << weightIt))->str();
                    string weightHistoName =
                        ("weight" + weightStr + "_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str();
                    // cout << weightHistoName << endl;
                    if(binContentMin > histo1D[weightHistoName]->GetBinContent(binN))
                        binContentMin = histo1D[weightHistoName]->GetBinContent(binN);
                    if(binContentMax < histo1D[weightHistoName]->GetBinContent(binN))
                        binContentMax = histo1D[weightHistoName]->GetBinContent(binN);
                    // cout << "binContentMax: " << binContentMax << "binContentMin: " << binContentMin << endl;
                    // cout<<"bin number : "<<binN<<"   bincontent: "<<histo1D["weight0"]->GetBinContent(binN)<<endl;
                }
                histo1D[("weightPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->SetBinContent(binN, binContentMax);
                histo1D[("weightMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->SetBinContent(binN, binContentMin);
            }
            /*
            errorfile->cd();
            errorfile->mkdir(("MultiSamplePlot_" + sVarofinterest + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            errorfile->cd(("MultiSamplePlot_" + sVarofinterest + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weightMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write("Minus");
            histo1D[("weightPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write("Plus");
            histo1D[("weight0_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write("Nominal");
            cout << "wrote weights in errorfile" << endl;
            */
            shapefile->cd();
            string MEScalesysname = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__ttbarTTX__ttMEScale";
            // cout << MEScalesysname << endl;
            histo1D[("weightMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "Down").c_str());
            histo1D[("weightPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "Up").c_str());
            cout << "wrote sys MEScale shapes in shapefile" << endl;
        }
    }
}
void GetMatchingSplit2(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string xmlNom,
    string CraneenPath,
    string mainTTbarSample,
    string otherTTbarsample,
    string sSplitVar1,
    float fbSplit1,
    float ftSplit1,
    float fwSplit1,
    string sSplitVar2,
    float fbSplit2,
    float ftSplit2,
    float fwSplit2)
{
    string plotname; ///// Jet Split plot
    string numStr1;
    string numStr2;
    string sbSplit1 = static_cast<ostringstream*>(&(ostringstream() << fbSplit1))->str();
    string stSplit1 = static_cast<ostringstream*>(&(ostringstream() << ftSplit1))->str();
    string swSplit1 = static_cast<ostringstream*>(&(ostringstream() << fwSplit1))->str();
    string sbSplit2 = static_cast<ostringstream*>(&(ostringstream() << fbSplit2))->str();
    string stSplit2 = static_cast<ostringstream*>(&(ostringstream() << ftSplit2))->str();
    string swSplit2 = static_cast<ostringstream*>(&(ostringstream() << fwSplit2))->str();

    cout << "Producing envelope for ttGenerator uncertainty" << endl;

    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        for(int t2 = fbSplit2; t2 <= ftSplit2; t2 += fwSplit2) {
            numStr2 = static_cast<ostringstream*>(&(ostringstream() << t2))->str();

            histo1D[("ttGeneratorPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                new TH1F(("Plus_match" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "Plus", nBins, plotLow, plotHigh);
            histo1D[("ttGeneratorMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                new TH1F(("Minus_match" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "Minus", nBins, plotLow, plotHigh);

            histo1D["main_ttbar"] = (TH1F*)shapefile->Get(
                (channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + mainTTbarSample + "__nominal").c_str());
            histo1D["other_ttbar"] = (TH1F*)shapefile->Get(
                (channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + otherTTbarsample + "__nominal").c_str());
            cout << "Got ttGenerator histos" << endl;
            // cout << channel+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + mainTTbarSample +
            // "__nominal"<<endl;
            // cout<< "    " << channel+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + otherTTbarsample +
            // "__nominal" << endl;
            for(int binN = 1; binN < nBins + 1; ++binN) {
                float binContentMax = -1, binContentMin = 1000000000000000;
                float errorMatching =
                    abs(histo1D["main_ttbar"]->GetBinContent(binN) - histo1D["other_ttbar"]->GetBinContent(binN));

                histo1D[("ttGeneratorPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->SetBinContent(
                    binN, histo1D["main_ttbar"]->GetBinContent(binN) + errorMatching);
                histo1D[("ttGeneratorMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->SetBinContent(
                    binN, histo1D["main_ttbar"]->GetBinContent(binN) - errorMatching);
            }

            shapefile->cd();
            string ttGeneratorsysname = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + mainTTbarSample + "__ttGenerator";
            histo1D[("ttGeneratorMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((ttGeneratorsysname + "Down").c_str());
            histo1D[("ttGeneratorPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((ttGeneratorsysname + "Up").c_str());
            cout << "wrote sys ttGenerator shapes in shapefile" << endl;
        }
    }
}


void DatasetPlotter(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string xmlNom,
    string CraneenPath,
    string shapefileName,
    string units)
{
    cout << "" << endl;
    cout << "RUNNING NOMINAL DATASETS" << endl;
    cout << "" << endl;
    shapefile->cd();
    errorfile->mkdir(("MultiSamplePlot_" + sVarofinterest).c_str());

    const char* xmlfile = xmlNom.c_str();
    cout << "used config file: " << xmlfile << endl;

    string pathPNG = "FourTop_Light";
    pathPNG += leptoAbbr;
    pathPNG += "_MSPlots/";
    mkdir(pathPNG.c_str(), 0777); // cout <<"Making directory :"<< pathPNG  <<endl;		//make directory

    ///////////////////////////////////////////    Load Datasets    /////////////////////////////////////
    TTreeLoader treeLoader;
    vector<Dataset*> datasets;
    treeLoader.LoadDatasets(datasets, xmlfile);
    //***************************************************CREATING
    // PLOTS****************************************************
    string plotname = sVarofinterest; ///// Non Jet Split plot
    string plotaxis = plotVarNames(sVarofinterest);

    //***********************************************OPEN FILES & GET
    // NTUPLES**********************************************
    string dataSetName, filepath;
    int nEntries;
    float ScaleFactor = 1, NormFactor = 1, Luminosity, varofInterest, GenWeight = 1, weight1 = 1, weight2 = 1,
          weight3 = 1, weight4 = 1, weight5 = 1, weight6 = 1, weight7 = 1, weight8 = 1, ttbar_flav = 1, SFtrigger = 1,
          SFlepton = 1, SFPU = 1, SFPU_up = 1, SFPU_down = 1, SFTopPt = 1, SFTopPt_up = 1, SFTopPt_down = 1, SFbehrends = 1,
          nJet = 1, SFalphaTune = 1, SFbtagCSV = 1, btagWeightCSVLFUp = 1, btagWeightCSVLFDown = 1, btagWeightCSVHFUp = 1,
          btagWeightCSVHFDown = 1, btagWeightCSVHFStats1Up = 1, btagWeightCSVHFStats1Down = 1,
          btagWeightCSVHFStats2Up = 1, btagWeightCSVHFStats2Down = 1, btagWeightCSVLFStats1Up = 1,
          btagWeightCSVLFStats1Down = 1, btagWeightCSVLFStats2Up = 1, btagWeightCSVLFStats2Down = 1,
          btagWeightCSVCFErr1Up = 1, btagWeightCSVCFErr1Down = 1, btagWeightCSVCFErr2Up = 1, btagWeightCSVCFErr2Down = 1,
          hdamp_up = 1, hdamp_down = 1, ttXrew = 1, ttXrew_up = 1, ttXrew_down = 1, weight_ct10 = 1, weight_mmht14 = 1;

    Dataset* ttbar_ll;
    Dataset* ttbar_ll_up;
    Dataset* ttbar_ll_down;
    Dataset* ttbar_cc;
    Dataset* ttbar_cc_up;
    Dataset* ttbar_cc_down;
    Dataset* ttbar_bb;
    Dataset* ttbar_bb_up;
    Dataset* ttbar_bb_down;

    string mainTTbarSample, otherTTbarsample;
    string chanText;
    cout << "channel  " << channel << endl;
    if(channel == "ttttmu" || channel == "ttttel") {
        mainTTbarSample = "TTJets_powheg";
        otherTTbarsample = "TTJets_MLM";
    } else {
        mainTTbarSample = "TTJetsPowheg";
        otherTTbarsample = "TTJetsMG";
    }
    if(channel == "ttttmu")
        chanText = "Single Lepton: #mu";
    else if(channel == "ttttel")
        chanText = "Single Lepton: e";
    else if(channel == "ttttmumu"){
        chanText = "Dilepton: #mu#mu";
        Luminosity = 5743.725979478
		+2573.399420069
		+4248.383597366
		+4009.132398404
		+3101.618412335
		+7540.487735974
		+8390.540446658+215.149415251
		;
    } else if(channel == "ttttmuel"){
        chanText = "Dilepton: e#mu";
        Luminosity = 5743.725979478
                +2573.399420069
                +4248.383597366
                +4009.132398404
                +3101.618412335
                +7540.487735974
                +8390.540446658+215.149415251
                ;
    } else if(channel == "ttttelel"){
        chanText = "Dilepton: ee";
        Luminosity = 5747.595589414
		+2573.399420069
		+4248.383597366
		+4009.132315299
		+3101.618412335
		+7540.487715338
		+8390.540368893+215.149415251
		;
    } else if(channel == "comb"){
        chanText = "Dilepton: Combined";
        Luminosity = 36550.0;
    }

    if(split_ttbar) {
        int ndatasets = datasets.size();
        cout << " - splitting TTBar dataset ..." << ndatasets << endl;
        vector<string> ttbar_filenames = datasets[ndatasets - 1]->Filenames();
        cout << "ttbar filenames =  " << ttbar_filenames[0] << endl;

        ttbar_ll = new Dataset("TTJets_ll", "tt + ll", true, 632, 1, 2, 1, 213.4, ttbar_filenames);
        ttbar_cc = new Dataset("TTJets_cc", "tt + cc", true, 633, 1, 2, 1, 6.9, ttbar_filenames);
        ttbar_bb = new Dataset("TTJets_bb", "tt + bb", true, 634, 1, 2, 1, 4.8, ttbar_filenames);

        // ttbar_ll_up = new Dataset("TTJets_ll_up", "tt + ll_up", true, 633, 2, 2, 1, 213.4, ttbar_filenames);
        // ttbar_cc_up = new Dataset("TTJets_cc_up", "tt + cc_up", true, 633, 2, 2, 1, 6.9, ttbar_filenames);
        // ttbar_bb_up = new Dataset("TTJets_bb_up", "tt + bb_up", true, 633, 2, 2, 1, 4.8, ttbar_filenames);

        // ttbar_ll_down = new Dataset("TTJets_ll_down", "tt + ll_down", true, 633, 2, 2, 1, 213.4, ttbar_filenames);
        // ttbar_cc_down = new Dataset("TTJets_cc_down", "tt + cc_down", true, 633, 2, 2, 1, 6.9, ttbar_filenames);
        // ttbar_bb_down = new Dataset("TTJets_bb_down", "tt + bb_down", true, 633, 2, 2, 1, 4.8, ttbar_filenames);

        /// heavy flav re-weight -> scaling ttbb up and ttjj down so that ttbb/ttjj matches CMS measurement.

        int newlumi = 439773.673896;//datasets[ndatasets - 1]->EquivalentLumi();
        ttbar_ll->SetEquivalentLuminosity(newlumi);
        ttbar_cc->SetEquivalentLuminosity(newlumi);
        ttbar_bb->SetEquivalentLuminosity(newlumi);
        // ttbar_ll_up->SetEquivalentLuminosity(newlumi);
        // ttbar_cc_up->SetEquivalentLuminosity(newlumi);
        // ttbar_bb_up->SetEquivalentLuminosity(newlumi);
        // ttbar_ll_down->SetEquivalentLuminosity(newlumi);
        // ttbar_cc_down->SetEquivalentLuminosity(newlumi);
        // ttbar_bb_down->SetEquivalentLuminosity(newlumi);

        //        ttbar_ll->SetEquivalentLuminosity(newlumi / ll_rw);
        //        ttbar_cc->SetEquivalentLuminosity(newlumi / ll_rw);
        //        ttbar_bb->SetEquivalentLuminosity(newlumi / bb_rw);
        //        ttbar_ll_up->SetEquivalentLuminosity(newlumi / ll_rw_up);
        //        ttbar_cc_up->SetEquivalentLuminosity(newlumi / ll_rw_up);
        //        ttbar_bb_up->SetEquivalentLuminosity(newlumi / bb_rw_up);
        //        ttbar_ll_down->SetEquivalentLuminosity(newlumi / ll_rw_down);
        //        ttbar_cc_down->SetEquivalentLuminosity(newlumi / ll_rw_down);
        //        ttbar_bb_down->SetEquivalentLuminosity(newlumi / bb_rw_down);

        ttbar_ll->SetColor(kRed);
        ttbar_cc->SetColor(kRed - 3);
        ttbar_bb->SetColor(kRed + 2);

        // datasets.pop_back();
        datasets.push_back(ttbar_bb);
        datasets.push_back(ttbar_cc);
        datasets.push_back(ttbar_ll);
        // datasets.push_back(ttbar_bb_up);
        // datasets.push_back(ttbar_cc_up);
        // datasets.push_back(ttbar_ll_up);
        // datasets.push_back(ttbar_bb_down);
        // datasets.push_back(ttbar_cc_down);
        // datasets.push_back(ttbar_ll_down);
    }
    MSPlot[plotname] = new MultiSamplePlot(datasets, plotname.c_str(), nBins, plotLow, plotHigh, plotaxis.c_str(), units, "Events", chanText.c_str());
    MSPlot[plotname]->setPreliminary(prelim_);  //toggels the preliminary text
    histo1D["TTJets_Rare"] = new TH1F("TTJets_Rare", "TTJets_Rare", nBins, plotLow, plotHigh);
    // instantiating these plots outside the dataset loop so that they can be combined between multiple channels of the
    // same main ttbar sample
    histo1D["Genweight_tt"] = new TH1F("Genweight", "Genweight", nBins, plotLow, plotHigh);
    histo1D["weight1_tt"] = new TH1F("weight1", "weight1", nBins, plotLow, plotHigh);
    histo1D["weight2_tt"] = new TH1F("weight2", "weight2", nBins, plotLow, plotHigh);
    histo1D["weight3_tt"] = new TH1F("weight3", "weight3", nBins, plotLow, plotHigh);
    histo1D["weight4_tt"] = new TH1F("weight4", "weight4", nBins, plotLow, plotHigh);
    histo1D["weight5_tt"] = new TH1F("weight5", "weight5", nBins, plotLow, plotHigh);
    histo1D["weight6_tt"] = new TH1F("weight6", "weight6", nBins, plotLow, plotHigh);
    histo1D["weight7_tt"] = new TH1F("weight7", "weight7", nBins, plotLow, plotHigh);
    histo1D["weight8_tt"] = new TH1F("weight8", "weight8", nBins, plotLow, plotHigh);
    histo1D["PU_Up"] = new TH1F("PU_Up", "PU_Up", nBins, plotLow, plotHigh);
    histo1D["PU_Down"] = new TH1F("PU_Down", "PU_Down", nBins, plotLow, plotHigh);
    histo1D["hdamp_Up"] = new TH1F("hdamp_Up", "hdamp_Up", nBins, plotLow, plotHigh);
    histo1D["hdamp_Down"] = new TH1F("hdamp_Down", "hdamp_Down", nBins, plotLow, plotHigh);
    histo1D["TTPT_Up"] = new TH1F("TTPT_Up", "TTPT_Up", nBins, plotLow, plotHigh);
    histo1D["TTPT_Down"] = new TH1F("TTPT_Down", "TTPT_Down", nBins, plotLow, plotHigh);
    histo1D["heavyFlav_Up"] = new TH1F("heavyFlav_Up", "heavyFlav_Up", nBins, plotLow, plotHigh);
    histo1D["heavyFlav_Down"] = new TH1F("heavyFlav_Down", "heavyFlav_Down", nBins, plotLow, plotHigh);
    histo1D["TTJetsPDF_Up"] = new TH1F("TTJetsPDF_Up", "TTJetsPDF_Up", nBins, plotLow, plotHigh);
    histo1D["TTJetsPDF_Down"] = new TH1F("TTJetsPDF_Down", "TTJetsPDF_Down", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVLF_Up"] = new TH1F("btagWeightCSVLF_Up", "btagWeightCSVLF_Up", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVLF_Down"] = new TH1F("btagWeightCSVLF_Down", "btagWeightCSVLF_Down", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVHF_Up"] = new TH1F("btagWeightCSVHF_Up", "btagWeightCSVHF_Up", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVHF_Down"] = new TH1F("btagWeightCSVHF_Down", "btagWeightCSVHF_Down", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVHFStats1_Up"] = new TH1F("btagWeightCSVHFStats1_Up", "btagWeightCSVHFStats1_Up", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVHFStats1_Down"] = new TH1F("btagWeightCSVHFStats1_Down", "btagWeightCSVHFStats1_Down", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVHFStats2_Up"] = new TH1F("btagWeightCSVHFStats2_Up", "btagWeightCSVHFStats2_Up", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVHFStats2_Down"] = new TH1F("btagWeightCSVHFStats2_Down", "btagWeightCSVHFStats2_Down", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVLFStats1_Up"] = new TH1F("btagWeightCSVLFStats1_Up", "btagWeightCSVLFStats1_Up", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVLFStats1_Down"] = new TH1F("btagWeightCSVLFStats1_Down", "btagWeightCSVLFStats1_Down", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVLFStats2_Up"] = new TH1F("btagWeightCSVLFStats2_Up", "btagWeightCSVLFStats2_Up", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVLFStats2_Down"] = new TH1F("btagWeightCSVLFStats2_Down", "btagWeightCSVLFStats2_Down", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVCFErr1_Up"] = new TH1F("btagWeightCSVCFErr1_Up", "btagWeightCSVCFErr1_Up", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVCFErr1_Down"] = new TH1F("btagWeightCSVCFErr1_Down", "btagWeightCSVCFErr1_Down", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVCFErr2_Up"] = new TH1F("btagWeightCSVCFErr2_Up", "btagWeightCSVCFErr2_Up", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVCFErr2_Down"] = new TH1F("btagWeightCSVCFErr2_Down", "btagWeightCSVCFErr2_Down", nBins, plotLow, plotHigh);

    histo1D["Genweight_tttt"] = new TH1F("Genweight_tttt", "Genweight_tttt", nBins, plotLow, plotHigh);
    histo1D["weight1_tttt"] = new TH1F("weight1_tttt", "weight1_tttt", nBins, plotLow, plotHigh);
    histo1D["weight2_tttt"] = new TH1F("weight2_tttt", "weight2_tttt", nBins, plotLow, plotHigh);
    histo1D["weight3_tttt"] = new TH1F("weight3_tttt", "weight3_tttt", nBins, plotLow, plotHigh);
    histo1D["weight4_tttt"] = new TH1F("weight4_tttt", "weight4_tttt", nBins, plotLow, plotHigh);
    histo1D["weight5_tttt"] = new TH1F("weight5_tttt", "weight5_tttt", nBins, plotLow, plotHigh);
    histo1D["weight6_tttt"] = new TH1F("weight6_tttt", "weight6_tttt", nBins, plotLow, plotHigh);
    histo1D["weight7_tttt"] = new TH1F("weight7_tttt", "weight7_tttt", nBins, plotLow, plotHigh);
    histo1D["weight8_tttt"] = new TH1F("weight8_tttt", "weight8_tttt", nBins, plotLow, plotHigh);
    histo1D["PU_Up_tttt"] = new TH1F("PU_Up_tttt", "PU_Up_tttt", nBins, plotLow, plotHigh);
    histo1D["PU_Down_tttt"] = new TH1F("PU_Down_tttt", "PU_Down_tttt", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVLF_Up_tttt"] = new TH1F("btagWeightCSVLF_Up_tttt", "btagWeightCSVLF_Up_tttt", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVLF_Down_tttt"] = new TH1F("btagWeightCSVLF_Down_tttt", "btagWeightCSVLF_Down_tttt", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVHF_Up_tttt"] = new TH1F("btagWeightCSVHF_Up_tttt", "btagWeightCSVHF_Up_tttt", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVHF_Down_tttt"] = new TH1F("btagWeightCSVHF_Down_tttt", "btagWeightCSVHF_Down_tttt", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVHFStats1_Up_tttt"] = new TH1F("btagWeightCSVHFStats1_Up_tttt", "btagWeightCSVHFStats1_Up_tttt", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVHFStats1_Down_tttt"] = new TH1F("btagWeightCSVHFStats1_Down_tttt", "btagWeightCSVHFStats1_Down_tttt", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVHFStats2_Up_tttt"] = new TH1F("btagWeightCSVHFStats2_Up_tttt", "btagWeightCSVHFStats2_Up_tttt", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVHFStats2_Down_tttt"] = new TH1F("btagWeightCSVHFStats2_Down_tttt", "btagWeightCSVHFStats2_Down_tttt", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVLFStats1_Up_tttt"] = new TH1F("btagWeightCSVLFStats1_Up_tttt", "btagWeightCSVLFStats1_Up_tttt", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVLFStats1_Down_tttt"] = new TH1F("btagWeightCSVLFStats1_Down_tttt", "btagWeightCSVLFStats1_Down_tttt", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVLFStats2_Up_tttt"] = new TH1F("btagWeightCSVLFStats2_Up_tttt", "btagWeightCSVLFStats2_Up_tttt", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVLFStats2_Down_tttt"] = new TH1F("btagWeightCSVLFStats2_Down_tttt", "btagWeightCSVLFStats2_Down_tttt", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVCFErr1_Up_tttt"] = new TH1F("btagWeightCSVCFErr1_Up_tttt", "btagWeightCSVCFErr1_Up_tttt", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVCFErr1_Down_tttt"] = new TH1F("btagWeightCSVCFErr1_Down_tttt", "btagWeightCSVCFErr1_Down_tttt", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVCFErr2_Up_tttt"] = new TH1F("btagWeightCSVCFErr2_Up_tttt", "btagWeightCSVCFErr2_Up_tttt", nBins, plotLow, plotHigh);
    histo1D["btagWeightCSVCFErr2_Down_tttt"] = new TH1F("btagWeightCSVCFErr2_Down_tttt", "btagWeightCSVCFErr2_Down_tttt", nBins, plotLow, plotHigh);

    for(int d = 0; d < datasets.size(); d++) // Loop through datasets
    {
        dataSetName = datasets[d]->Name();
        cout << "Dataset:  :" << dataSetName << endl;
        if(dataSetName.find("TTJets_ll") != string::npos || dataSetName.find("TTJets_cc") != string::npos || dataSetName.find("TTJets_bb") != string::npos) {
            cout << "skip ttbar split datasets!" << endl;
            continue;
        }

        filepath = CraneenPath + dataSetName + "_Run2_TopTree_Study.root"; // cout<<"filepath: "<<filepath<<endl;
        FileObj[dataSetName.c_str()] = new TFile((filepath).c_str()); // create TFile for each dataset
        string nTuplename;
        nTuplename = "Craneen__" + leptoAbbr;
        nTuple[dataSetName.c_str()] = (TNtuple*)FileObj[dataSetName.c_str()]->Get(nTuplename.c_str()); // get ntuple for each dataset
        nEntries = (int)nTuple[dataSetName.c_str()]->GetEntries();
        cout << "                 nEntries: " << nEntries << endl;

        if(sVarofinterest.find("nJets") != string::npos) {
            nTuple[dataSetName.c_str()]->SetBranchAddress("nJets", &nJet);
        }
        nTuple[dataSetName.c_str()]->SetBranchAddress(sVarofinterest.c_str(), &varofInterest);
        nTuple[dataSetName.c_str()]->SetBranchAddress("ScaleFactor", &ScaleFactor);
        nTuple[dataSetName.c_str()]->SetBranchAddress("NormFactor", &NormFactor);
        nTuple[dataSetName.c_str()]->SetBranchAddress("GenWeight", &GenWeight);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight1", &weight1);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight2", &weight2);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight3", &weight3);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight4", &weight4);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight5", &weight5);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight6", &weight6);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight7", &weight7);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight8", &weight8);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFlepton", &SFlepton);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFtrigger", &SFtrigger);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFbtagCSV", &SFbtagCSV); // SFbtag
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVLFUp", &btagWeightCSVLFUp);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVLFDown", &btagWeightCSVLFDown);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVHFUp", &btagWeightCSVHFUp);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVHFDown", &btagWeightCSVHFDown);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVHFStats1Up", &btagWeightCSVHFStats1Up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVHFStats1Down", &btagWeightCSVHFStats1Down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVHFStats2Up", &btagWeightCSVHFStats2Up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVHFStats2Down", &btagWeightCSVHFStats2Down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVLFStats1Up", &btagWeightCSVLFStats1Up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVLFStats1Down", &btagWeightCSVLFStats1Down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVLFStats2Up", &btagWeightCSVLFStats2Up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVLFStats2Down", &btagWeightCSVLFStats2Down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVCFErr1Up", &btagWeightCSVCFErr1Up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVCFErr1Down", &btagWeightCSVCFErr1Down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVCFErr2Up", &btagWeightCSVCFErr2Up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVCFErr2Down", &btagWeightCSVCFErr2Down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFPU", &SFPU);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFPU_up", &SFPU_up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFPU_down", &SFPU_down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("ttXrew", &ttXrew);
        nTuple[dataSetName.c_str()]->SetBranchAddress("ttXrew_up", &ttXrew_up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("ttXrew_down", &ttXrew_down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFtopPt", &SFTopPt);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFtopPtUp", &SFTopPt_up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFtopPtDown", &SFTopPt_down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight_ct10", &weight_ct10);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight_mmht14", &weight_mmht14);
        nTuple[dataSetName.c_str()]->SetBranchAddress("hdampup", &hdamp_up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("hdampdown", &hdamp_down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("ttbar_flav", &ttbar_flav);
        // 
        //
        //
        float eqlumi = 1. / datasets[d]->EquivalentLumi();
        cout << "eqlumi: " << eqlumi << endl;

        histo1D[dataSetName.c_str()] = new TH1F(dataSetName.c_str(), dataSetName.c_str(), nBins, plotLow, plotHigh);
        ////////////////////////////////////////////////////////
        /////       loop through entries and fill plots    /////
        ////////////////////////////////////////////////////////

        //Luminosity = 36000;

        float ProjectedLumi = 10000; // pb-1
        float LumiFactor = 1;
        // float LumiFactor = ProjectedLumi/Luminosity;

        for(int j = 0; j < nEntries; j++) {
            nTuple[dataSetName.c_str()]->GetEntry(j);

            if(sVarofinterest.find("thJetPt") != string::npos && varofInterest < 0) continue;
            SFbehrends = 1;
            SFalphaTune = 1;
            NormFactor = 1;
            //SFTopPt = 1; SFTopPt_up = 1; SFTopPt_down = 1;
            if(dataSetName.find("tttt") != string::npos) {
                NormFactor = 1.0 / 0.4214;
            }
            else if(dataSetName.find("TTJets_aMCatNLO") != string::npos) {
                NormFactor = 1.0 / 0.3304;
            }

            float ttbbReweight = 1, ttbbReweight_up = 1, ttbbReweight_down = 1;
            if(reweight_ttbar && dataSetName.find("TTJets") != string::npos) {
                //if(ttXrew>1) ttbbReweight = 1.714;
                //else ttbbReweight = 0.9899;
                //ttbbReweight = ttXrew;
                if(ttXrew>1.1){
                    ttbbReweight_up = 1.35;//ttXrew_up;
                    ttbbReweight_down = 0.65;//ttXrew_down;
                }
            }


            //float cFactor = 1, cFactor_up = 1, cFactor_down = 1;

            //if(splitVar1 == 6){ cFactor = 0.9; cFactor_up = 0.93; cFactor_down = 0.87;}
            //if(splitVar1 == 7){ cFactor = 0.85; cFactor_up = 0.89; cFactor_down = 0.81;}
            //if(splitVar1 >=8){ cFactor = 0.85; cFactor_up = 0.935; cFactor_down = 0.765;}

            ////////////////////////////////////////////////////////
            /////                    Fill plots                /////
            ////////////////////////////////////////////////////////


            if((dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
                dataSetName.find("DATA") != string::npos || dataSetName.find("NP_overlay_Data") != string::npos) &&
               (dataSetName.find("Pseudo") == string::npos || dataSetName.find("pseudo") == string::npos)) {

                histo1D[dataSetName.c_str()]->Fill(varofInterest, 1);
                ////////DATA BLINDED ////
                MSPlot[plotname]->Fill(varofInterest, datasets[d], true, 1);

            } else {
                if(lScale > 0) // artificial Lumi
                {
                    Luminosity = 1000 * lScale;
                }
                if(dataSetName.find(mainTTbarSample) != string::npos && dataSetName.find("JES") == string::npos &&
                   dataSetName.find("JER") == string::npos && dataSetName.find("Up") == string::npos &&
                   dataSetName.find("Down") == string::npos  && dataSetName.find("ISR") == string::npos &&
                   dataSetName.find("FSR") == string::npos) {
                    // Since these are instantiated outside the dataset loop, these will combine across multiple
                    // channels of the mainTTbarSample and provide the correct histos for the MEScale envelope
                    histo1D["Genweight_tt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["weight1_tt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * weight1 * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["weight2_tt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * weight2 * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["weight3_tt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * weight3 * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["weight4_tt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * weight4 * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["weight5_tt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * weight5 * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["weight6_tt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * weight6 * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["weight7_tt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * weight7 * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["weight8_tt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * weight8 * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVLF_Up"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFUp * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVLF_Down"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFDown * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVHF_Up"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFUp * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVHF_Down"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFDown * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVHFStats1_Up"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats1Up * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVHFStats1_Down"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats1Down * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVHFStats2_Up"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats2Up * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVHFStats2_Down"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats2Down * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVLFStats1_Up"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats1Up * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVLFStats1_Down"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats1Down * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVLFStats2_Up"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats2Up * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVLFStats2_Down"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats2Down * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVCFErr1_Up"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr1Up * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVCFErr1_Down"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr1Down * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVCFErr2_Up"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr2Up * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVCFErr2_Down"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr2Down * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["PU_Up"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU_up *
                             SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["PU_Down"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU_down *
                             SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["TTPT_Up"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU *
                             SFTopPt_up * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["TTPT_Down"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU *
                             SFTopPt_down * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["TTJetsPDF_Up"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU *
                             SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor * findmax(weight_ct10, weight_mmht14, (float) 1.0));
                    histo1D["TTJetsPDF_Down"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU *
                             SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor * findmin(weight_ct10, weight_mmht14, (float) 1.0));
                    histo1D["heavyFlav_Up"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight_up * LumiFactor);
                    histo1D["heavyFlav_Down"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight_down * LumiFactor);
                    histo1D["hdamp_Up"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * hdamp_up *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["hdamp_Down"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * hdamp_down *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);

                    histo1D[dataSetName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * GenWeight * Luminosity * eqlumi * ttbbReweight);
                    if(split_ttbar) {
                        if(ttXrew < 1) { 
                            MSPlot[plotname]->Fill(varofInterest, ttbar_ll, true, NormFactor * GenWeight * SFtrigger * SFlepton *
                             SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor);
                        } else if(ttXrew > 1) {
                            MSPlot[plotname]->Fill(varofInterest, ttbar_bb, true, NormFactor * GenWeight * SFtrigger * SFlepton *
                             SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor);
                        } else {
                            MSPlot[plotname]->Fill(varofInterest, ttbar_cc, true, NormFactor * GenWeight * SFtrigger * SFlepton *
                             SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor);
                        }
                    } else {
                        MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * GenWeight * SFtrigger * SFlepton *
                             SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor);
                    }
                } else if(dataSetName.find("NP_overlay_ttttNLO") != string::npos && dataSetName.find("JES") == string::npos &&
                          dataSetName.find("JER") == string::npos && dataSetName.find("Up") == string::npos &&
                          dataSetName.find("Down") == string::npos && dataSetName.find("FSR") == string::npos && dataSetName.find("ISR") == string::npos) {
                    MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * GenWeight * SFtrigger * SFlepton *
                             SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor);

                    histo1D["Genweight_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["weight1_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * weight1 * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["weight2_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * weight2 * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["weight3_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * weight3 * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["weight4_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * weight4 * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["weight5_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * weight5 * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["weight6_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * weight6 * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["weight7_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * weight7 * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["weight8_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * weight8 * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVLF_Up_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFUp * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVLF_Down_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFDown * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVHF_Up_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFUp * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVHF_Down_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFDown * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVHFStats1_Up_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats1Up * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVHFStats1_Down_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats1Down * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVHFStats2_Up_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats2Up * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVHFStats2_Down_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats2Down * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVLFStats1_Up_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats1Up * SFalphaTune * 
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVLFStats1_Down_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats1Down * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVLFStats2_Up_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats2Up * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVLFStats2_Down_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats2Down * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVCFErr1_Up_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr1Up * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVCFErr1_Down_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr1Down * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVCFErr2_Up_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr2Up * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["btagWeightCSVCFErr2_Down_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr2Down * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["PU_Up_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU_up *
                             SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D["PU_Down_tttt"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU_down *
                             SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);

                    histo1D[dataSetName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * GenWeight * Luminosity * eqlumi * ttbbReweight);
                } else if(dataSetName.find("Rare1") != string::npos || dataSetName.find("Rare2") != string::npos) {
                    histo1D["TTJets_Rare"]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * GenWeight * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor);
                } else if(dataSetName.find(otherTTbarsample) == string::npos && dataSetName.find("Down")==string::npos &&
                        dataSetName.find("Scale") == string::npos && dataSetName.find("JES") == string::npos &&
                        dataSetName.find("JER") == string::npos && dataSetName.find("Up") == string::npos &&
                        dataSetName.find("ScaleH") == string::npos && dataSetName.find("TTUE") == string::npos &&
                        dataSetName.find("ISR") == string::npos && dataSetName.find("FSR") == string::npos) { 
                    // ie. don't add the MLM dataset which is just used for ttGenerator
 
                    MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * GenWeight * SFtrigger * SFlepton *
                             SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor);
                    histo1D[dataSetName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                             SFPU * SFTopPt * SFbehrends * GenWeight * Luminosity * eqlumi * ttbbReweight);

                } else {
                    histo1D[dataSetName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * 
                             SFPU * SFTopPt * SFbehrends * GenWeight * Luminosity * eqlumi * ttbbReweight);
                }
            }
        } // end of event loop
        // cout<<"after for loop entries"<<endl;

        shapefile->cd();
        TCanvas* canv = new TCanvas();
        histo1D[dataSetName.c_str()]->Draw();
        string writename = "";
        if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos || dataSetName.find("DATA") != string::npos) {
            writename = channel + "__data_obs__nominal";
        } else if(dataSetName.find("TTJetsPowheg_JESUp") != string::npos) {
            writename = channel + "__" + "ttbarTTX" + "__JESUp";
        } else if(dataSetName.find("TTJetsPowheg_JESDown") != string::npos) {
            writename = channel + "__" + "ttbarTTX" + "__JESDown";
        } else if(dataSetName.find("TT_SubTotalPileUpUp") != string::npos) {
            writename = channel + "__" + "ttbarTTX" + "__SubTotalPileUpUp";
        } else if(dataSetName.find("TT_SubTotalPileUpDown") != string::npos) {
            writename = channel + "__" + "ttbarTTX" + "__SubTotalPileUpDown";
        } else if(dataSetName.find("TT_SubTotalRelativeUp") != string::npos) {
            writename = channel + "__" + "ttbarTTX" + "__SubTotalRelativeUp";
        } else if(dataSetName.find("TT_SubTotalRelativeDown") != string::npos) {
            writename = channel + "__" + "ttbarTTX" + "__SubTotalRelativeDown";
        } else if(dataSetName.find("TT_SubTotalPtUp") != string::npos) {
            writename = channel + "__" + "ttbarTTX" + "__SubTotalPtUp";
        } else if(dataSetName.find("TT_SubTotalPtDown") != string::npos) {
            writename = channel + "__" + "ttbarTTX" + "__SubTotalPtDown";
        } else if(dataSetName.find("TT_SubTotalScaleUp") != string::npos) {
            writename = channel + "__" + "ttbarTTX" + "__SubTotalScaleUp";
        } else if(dataSetName.find("TT_SubTotalScaleDown") != string::npos) {
            writename = channel + "__" + "ttbarTTX" + "__SubTotalScaleDown";
        } else if(dataSetName.find("TTJetsPowheg_JERUp") != string::npos) {
            writename = channel + "__" + "ttbarTTX" + "__JERUp";
        } else if(dataSetName.find("TTJetsPowheg_JERDown") != string::npos) {
            writename = channel + "__" + "ttbarTTX" + "__JERDown";
        } else if(dataSetName.find("TTUEUp") != string::npos) {
            writename = channel + "__" + "ttbarTTX" + "__TTUEUp";
        } else if(dataSetName.find("TTUEDown") != string::npos) {
            writename = channel + "__" + "ttbarTTX" + "__TTUEDown";
        } else if(dataSetName.find("TTISRUp") != string::npos) {
            writename = channel + "__" + "ttbarTTX" + "__TTISRUp";
        } else if(dataSetName.find("TTISRDown") != string::npos) {
            writename = channel + "__" + "ttbarTTX" + "__TTISRDown";
        } else if(dataSetName.find("TTFSRUp") != string::npos) {
            writename = channel + "__" + "ttbarTTX" + "__TTFSRUp";
        } else if(dataSetName.find("TTFSRDown") != string::npos) {
            writename = channel + "__" + "ttbarTTX" + "__TTFSRDown";
        } else if(dataSetName.find("ttttISRUp") != string::npos) {
            writename = channel + "__" + "NP_overlay_ttttNLO" + "__ttttISRUp";
        } else if(dataSetName.find("ttttISRDown") != string::npos) {
            writename = channel + "__" + "NP_overlay_ttttNLO" + "__ttttISRDown";
        } else if(dataSetName.find("ttttFSRUp") != string::npos) {
            writename = channel + "__" + "NP_overlay_ttttNLO" + "__ttttFSRUp";
        } else if(dataSetName.find("ttttFSRDown") != string::npos) {
            writename = channel + "__" + "NP_overlay_ttttNLO" + "__ttttFSRDown";
        } else if(dataSetName.find("JESUp") != string::npos && dataSetName.find("tttt") != string::npos) {
            writename = channel + "__" + "NP_overlay_ttttNLO" + "__JESUp";
        } else if(dataSetName.find("JESDown") != string::npos && dataSetName.find("tttt") != string::npos) {
            writename = channel + "__" + "NP_overlay_ttttNLO" + "__JESDown";
        } else if(dataSetName.find("JERUp") != string::npos && dataSetName.find("tttt") != string::npos) {
            writename = channel + "__" + "NP_overlay_ttttNLO" + "__JERUp";
        } else if(dataSetName.find("JERDown") != string::npos && dataSetName.find("tttt") != string::npos) {
            writename = channel + "__" + "NP_overlay_ttttNLO" + "__JERDown";
        } else if(dataSetName.find("ttttNLO_SubTotalPileUpUp") != string::npos) {
            writename = channel + "__" + "NP_overlay_ttttNLO" + "__SubTotalPileUpUp";
        } else if(dataSetName.find("ttttNLO_SubTotalPileUpDown") != string::npos) {
            writename = channel + "__" + "NP_overlay_ttttNLO" + "__SubTotalPileUpDown";
        } else if(dataSetName.find("ttttNLO_SubTotalRelativeUp") != string::npos) {
            writename = channel + "__" + "NP_overlay_ttttNLO" + "__SubTotalRelativeUp";
        } else if(dataSetName.find("ttttNLO_SubTotalRelativeDown") != string::npos) {
            writename = channel + "__" + "NP_overlay_ttttNLO" + "__SubTotalRelativeDown";
        } else if(dataSetName.find("ttttNLO_SubTotalPtUp") != string::npos) {
            writename = channel + "__" + "NP_overlay_ttttNLO" + "__SubTotalPtUp";
        } else if(dataSetName.find("ttttNLO_SubTotalPtDown") != string::npos) {
            writename = channel + "__" + "NP_overlay_ttttNLO" + "__SubTotalPtDown";
        } else if(dataSetName.find("ttttNLO_SubTotalScaleUp") != string::npos) {
            writename = channel + "__" + "NP_overlay_ttttNLO" + "__SubTotalScaleUp";
        } else if(dataSetName.find("ttttNLO_SubTotalScaleDown") != string::npos) {
            writename = channel + "__" + "NP_overlay_ttttNLO" + "__SubTotalScaleDown";
        } else if(dataSetName.find("TTJetsPowheg") != string::npos && dataSetName.find("Up") == string::npos && dataSetName.find("Down") == string::npos) {
            writename = channel + "__ttbarTTX" + "__nominal";
        } else {
            writename = channel + "__" + dataSetName + "__nominal";
        }
        histo1D[dataSetName.c_str()]->Write((writename).c_str());
        //canv->SaveAs((pathPNG + dataSetName + ".png").c_str());

        //string MEScalesysname = channel + "__ttbarTTX" + "__";

        if(dataSetName.find(mainTTbarSample) != string::npos && dataSetName.find("JES") == string::npos &&
            dataSetName.find("JER") == string::npos && dataSetName.find("Up") == string::npos &&
            dataSetName.find("Down") == string::npos && dataSetName.find("FSR") == string::npos &&
            dataSetName.find("ISR") == string::npos) {
            cout<<"  making weights histos"<<endl;

            histo1D["Genweight_tt"]->Write("Genweight_tt");
            for(int ii = 1; ii < 9; ii++) {
                // TCanvas *canv1 = new TCanvas();
                string weightstring = static_cast<ostringstream*>(&(ostringstream() << ii))->str();
                string weighthisto = "weight" + weightstring + "_tt";
                //cout << "weight histo:  " << weighthisto << " Max: " << histo1D[weighthisto]->GetMaximum() << endl;
                // histo1D[weighthisto]->Draw();
                histo1D[weighthisto]->Write(("weight" + weightstring + "_tt").c_str());
                // canv1->SaveAs(("weight"+weightstring+".png").c_str());
            }
            string MEScalesysname = channel + "__ttbarTTX" + "__";

            histo1D["PU_Up"]->Write((MEScalesysname + "PUUp").c_str());
            histo1D["PU_Down"]->Write((MEScalesysname + "PUDown").c_str());
            histo1D["TTPT_Up"]->Write((MEScalesysname + "TTPTUp").c_str());
            histo1D["TTPT_Down"]->Write((MEScalesysname + "TTPTDown").c_str());
            histo1D["TTJetsPDF_Up"]->Write((MEScalesysname + "TTJetsPDFUp").c_str());
            histo1D["TTJetsPDF_Down"]->Write((MEScalesysname + "TTJetsPDFDown").c_str());
            histo1D["hdamp_Up"]->Write((MEScalesysname + "TTJets_HDAMPUp").c_str());
            histo1D["hdamp_Down"]->Write((MEScalesysname + "TTJets_HDAMPDown").c_str());
            histo1D["heavyFlav_Up"]->Write((MEScalesysname + "heavyFlavUp").c_str());
            histo1D["heavyFlav_Down"]->Write((MEScalesysname + "heavyFlavDown").c_str());
            histo1D["btagWeightCSVLF_Up"]->Write((MEScalesysname + "btagWeightCSVLFUp").c_str());
            histo1D["btagWeightCSVLF_Down"]->Write((MEScalesysname + "btagWeightCSVLFDown").c_str());
            histo1D["btagWeightCSVHF_Up"]->Write((MEScalesysname + "btagWeightCSVHFUp").c_str());
            histo1D["btagWeightCSVHF_Down"]->Write((MEScalesysname + "btagWeightCSVHFDown").c_str());
            histo1D["btagWeightCSVHFStats1_Up"]->Write((MEScalesysname + "btagWeightCSVHFStats1Up").c_str());
            histo1D["btagWeightCSVHFStats1_Down"]->Write((MEScalesysname + "btagWeightCSVHFStats1Down").c_str());
            histo1D["btagWeightCSVHFStats2_Up"]->Write((MEScalesysname + "btagWeightCSVHFStats2Up").c_str());
            histo1D["btagWeightCSVHFStats2_Down"]->Write((MEScalesysname + "btagWeightCSVHFStats2Down").c_str());
            histo1D["btagWeightCSVLFStats1_Up"]->Write((MEScalesysname + "btagWeightCSVLFStats1Up").c_str());
            histo1D["btagWeightCSVLFStats1_Down"]->Write((MEScalesysname + "btagWeightCSVLFStats1Down").c_str());
            histo1D["btagWeightCSVLFStats2_Up"]->Write((MEScalesysname + "btagWeightCSVLFStats2Up").c_str());
            histo1D["btagWeightCSVLFStats2_Down"]->Write((MEScalesysname + "btagWeightCSVLFStats2Down").c_str());
            histo1D["btagWeightCSVCFErr1_Up"]->Write((MEScalesysname + "btagWeightCSVCFErr1Up").c_str());
            histo1D["btagWeightCSVCFErr1_Down"]->Write((MEScalesysname + "btagWeightCSVCFErr1Down").c_str());
            histo1D["btagWeightCSVCFErr2_Up"]->Write((MEScalesysname + "btagWeightCSVCFErr2Up").c_str());
            histo1D["btagWeightCSVCFErr2_Down"]->Write((MEScalesysname + "btagWeightCSVCFErr2Down").c_str());            
        }
        if(dataSetName.find("NP_overlay_tttt") != string::npos && dataSetName.find("JES") == string::npos &&
            dataSetName.find("JER") == string::npos && dataSetName.find("Up") == string::npos &&
            dataSetName.find("Down") == string::npos && dataSetName.find("FSR") == string::npos &&
            dataSetName.find("ISR") == string::npos) {

            histo1D["Genweight_tttt"]->Write("Genweight_tttt");

            for(int ii = 1; ii < 9; ii++) {
                // TCanvas *canv1 = new TCanvas();
                string weightstring = static_cast<ostringstream*>(&(ostringstream() << ii))->str();
                string weighthisto = "weight" + weightstring + "_tttt";
                //cout << "weight histo:  " << weighthisto << " Max: " << histo1D[weighthisto]->GetMaximum() << endl;
                // histo1D[weighthisto]->Draw();
                histo1D[weighthisto]->Write(("weight" + weightstring + "_tttt").c_str());
                // canv1->SaveAs(("weight"+weightstring+".png").c_str());
            }

            histo1D["PU_Up_tttt"]->Write((channel + "__NP_overlay_ttttNLO__PUUp").c_str());
            histo1D["PU_Down_tttt"]->Write((channel + "__NP_overlay_ttttNLO__PUDown").c_str());
            histo1D["btagWeightCSVLF_Up_tttt"]->Write((channel + "__NP_overlay_ttttNLO__btagWeightCSVLFUp").c_str());
            histo1D["btagWeightCSVLF_Down_tttt"]->Write((channel + "__NP_overlay_ttttNLO__btagWeightCSVLFDown").c_str());
            histo1D["btagWeightCSVHF_Up_tttt"]->Write((channel + "__NP_overlay_ttttNLO__btagWeightCSVHFUp").c_str());
            histo1D["btagWeightCSVHF_Down_tttt"]->Write((channel + "__NP_overlay_ttttNLO__btagWeightCSVHFDown").c_str());
            histo1D["btagWeightCSVHFStats1_Up_tttt"]->Write((channel + "__NP_overlay_ttttNLO__btagWeightCSVHFStats1Up").c_str());
            histo1D["btagWeightCSVHFStats1_Down_tttt"]->Write((channel + "__NP_overlay_ttttNLO__btagWeightCSVHFStats1Down").c_str());
            histo1D["btagWeightCSVHFStats2_Up_tttt"]->Write((channel + "__NP_overlay_ttttNLO__btagWeightCSVHFStats2Up").c_str());
            histo1D["btagWeightCSVHFStats2_Down_tttt"]->Write((channel + "__NP_overlay_ttttNLO__btagWeightCSVHFStats2Down").c_str());
            histo1D["btagWeightCSVLFStats1_Up_tttt"]->Write((channel + "__NP_overlay_ttttNLO__btagWeightCSVLFStats1Up").c_str());
            histo1D["btagWeightCSVLFStats1_Down_tttt"]->Write((channel + "__NP_overlay_ttttNLO__btagWeightCSVLFStats1Down").c_str());
            histo1D["btagWeightCSVLFStats2_Up_tttt"]->Write((channel + "__NP_overlay_ttttNLO__btagWeightCSVLFStats2Up").c_str());
            histo1D["btagWeightCSVLFStats2_Down_tttt"]->Write((channel + "__NP_overlay_ttttNLO__btagWeightCSVLFStats2Down").c_str());
            histo1D["btagWeightCSVCFErr1_Up_tttt"]->Write((channel + "__NP_overlay_ttttNLO__btagWeightCSVCFErr1Up").c_str());
            histo1D["btagWeightCSVCFErr1_Down_tttt"]->Write((channel + "__NP_overlay_ttttNLO__btagWeightCSVCFErr1Down").c_str());
            histo1D["btagWeightCSVCFErr2_Up_tttt"]->Write((channel + "__NP_overlay_ttttNLO__btagWeightCSVCFErr2Up").c_str());
            histo1D["btagWeightCSVCFErr2_Down_tttt"]->Write((channel + "__NP_overlay_ttttNLO__btagWeightCSVCFErr2Down").c_str());            
        }

        // cout<<"saved histos"<<endl;
        FileObj[dataSetName.c_str()]->Close();
    } // end of dataset loop

    histo1D["TTJets_Rare"]->Write((channel + "__TTRARE__nominal").c_str());

    GetScaleEnvelope_tttt(nBins, lScale, plotLow, plotHigh, leptoAbbr, shapefile, errorfile, channel, sVarofinterest, xmlNom, CraneenPath, shapefileName, mainTTbarSample);
    GetScaleEnvelope(nBins, lScale, plotLow, plotHigh, leptoAbbr, shapefile, errorfile, channel, sVarofinterest, xmlNom, CraneenPath, shapefileName, mainTTbarSample);
    GetErrorBand(nBins, lScale, plotLow, plotHigh, leptoAbbr, shapefile, errorfile, channel, sVarofinterest, xmlNom, CraneenPath, shapefileName, mainTTbarSample);
    //if(channel.find("comb") == string::npos)
    //GetMatching(nBins, lScale, plotLow, plotHigh, leptoAbbr, shapefile, errorfile, channel, sVarofinterest, xmlNom, CraneenPath, mainTTbarSample, otherTTbarsample);
    //cout << "produced envelope" << endl;
    errorfile->Close();

    //treeLoader.UnLoadDataset();
    cout << "Create MSPlots" << endl;
    string MEScaleFileDir = "ScaleFiles" + leptoAbbr + "_light";
    string MEScaleFileName = MEScaleFileDir + "/Error" + sVarofinterest + ".root";
    mkdir(MEScaleFileDir.c_str(), 0777);

    //MSPlot[plotname.c_str()]->setErrorBandFile((MEScaleFileName).c_str()); // set error file for uncertainty bands on multisample plot
    //MSPlot[plotname.c_str()]->setDataLumi(Luminosity);
    //if(plotname.find("Phi") != string::npos) MSPlot[plotname.c_str()]->setMaxY(60);

    for(map<string, MultiSamplePlot*>::const_iterator it = MSPlot.begin(); it != MSPlot.end(); it++) {
        string name = it->first;
        MultiSamplePlot* temp = it->second;
        temp->setDataLumi(35822);

        temp->setErrorBandFile(MEScaleFileName.c_str());
        temp->Draw(sVarofinterest.c_str(), 1, true, false, true, 20);
        temp->Write(shapefile, name, true, pathPNG, "eps");
        temp->Write(shapefile, name, true, pathPNG, "root");
    }
    MSPlot.erase(plotname);
    for(map<string, TH1F*>::const_iterator it = histo1D.begin(); it != histo1D.end(); it++) {
        histo1D.erase(it->first);
    }
};

void CutFlowPlotter(TFile* cffile,
    string leptoAbbr,
    string channel,
    string xmlNom,
    string CraneenPath,
    int nCuts,
    float lScale)
{
    const char* xmlfile = xmlNom.c_str();
    cout << "used config file: " << xmlfile << endl;

    string pathPNG = "FourTop_Light";
    string mainTTbarSample, otherTTbarsample;
    pathPNG += leptoAbbr;
    pathPNG += "_MSPlots/";
    mkdir(pathPNG.c_str(), 0777);
    cout << "Making directory :" << pathPNG << endl; // make directory
    if(channel == "ttttmu" || channel == "ttttel") {
        mainTTbarSample = "TTJets_powheg";
        otherTTbarsample = "TTJets_MLM";
    } else {
        mainTTbarSample = "TTJetsPowheg";
        otherTTbarsample = "TTJetsMG";
    }

    ///////////////////////////////////////////////////////////// Load Datasets
    ///////////////////////////////////////////////////////////////////////
    TTreeLoader treeLoader;
    vector<Dataset*> datasets;                  // cout<<"vector filled"<<endl;
    treeLoader.LoadDatasets(datasets, xmlfile); // cout<<"datasets loaded"<<endl;

    vector<string> CutsselecTable;
    string dataSetName, filepath;
    string plotname = channel + " Cut Flow";
    int nEntries;
    float ScaleFactor = 1, NormFactor = 1, Luminosity, varofInterest, GenWeight = 1, weight1 = 1, weight2 = 1,
          weight3 = 1, weight4 = 1, weight5 = 1, weight6 = 1, weight7 = 1, weight8 = 1, ttbar_flav = 1, SFtrigger = 1,
          SFlepton = 1, SFbtag_light = 1, SFbtag_lightUp = 1, SFbtag_lightDown = 1, SFbtag_heavy = 1,
          SFbtag_heavyUp = 1, SFbtag_heavyDown = 1, SFPU = 1, SFPU_up = 1, SFPU_down = 1, SFTopPt = 1, SFbehrends = 1,
          alphaTune = 1, nJets = 0;
    MultiSamplePlot* cutFlowPlot = new MultiSamplePlot(datasets, plotname.c_str(), nCuts, 0, nCuts, "Cut Number");
    cutFlowPlot->setPreliminary(prelim_);
    std::vector<float> cuts(nCuts);

    if(lScale > 0) // artificial Lumi
    {
        Luminosity = 1000 * lScale;
    }
    Luminosity = 36000.0;

    if(leptoAbbr.find("muel") != string::npos || leptoAbbr.find("MuEl") != string::npos) {
        CutsselecTable.push_back(string("initial"));
        CutsselecTable.push_back(string("Trigger"));
        CutsselecTable.push_back(string("At least 1 PV"));
        CutsselecTable.push_back(string("Exactly 1 Loose Isolated Muon"));
        CutsselecTable.push_back(string("Exactly 1 Loose Electron"));
        CutsselecTable.push_back(string("At least 2 Jets"));
        CutsselecTable.push_back(string("At least 3 Jets"));
        CutsselecTable.push_back(string("At least 4 Jets"));
        CutsselecTable.push_back(string("At least 2 CSVM Jets"));
        CutsselecTable.push_back(string("At Least 500 GeV HT"));
    } else if(leptoAbbr.find("mumu") != string::npos || leptoAbbr.find("MuMu") != string::npos) {
        CutsselecTable.push_back(string("initial"));
        CutsselecTable.push_back(string("Trigger"));
        CutsselecTable.push_back(string("At least 1 PV"));
        CutsselecTable.push_back(string("Exactly 2 Loose Isolated Muons"));
        CutsselecTable.push_back(string("Mass Veto"));
        CutsselecTable.push_back(string("At least 2 Jets"));
        CutsselecTable.push_back(string("At least 3 Jets"));
        CutsselecTable.push_back(string("At least 4 Jets"));
        CutsselecTable.push_back(string("At least 2 CSVM Jets"));
        CutsselecTable.push_back(string("At Least 500 GeV HT"));
    } else if(leptoAbbr.find("elel") != string::npos || leptoAbbr.find("ElEl") != string::npos) {
        CutsselecTable.push_back(string("initial"));
        CutsselecTable.push_back(string("Trigger"));
        CutsselecTable.push_back(string("At least 1 PV"));
        CutsselecTable.push_back(string("Exactly 2 Loose Electrons"));
        CutsselecTable.push_back(string("Mass Veto"));
        CutsselecTable.push_back(string("At least 2 Jets"));
        CutsselecTable.push_back(string("At least 3 Jets"));
        CutsselecTable.push_back(string("At least 4 Jets"));
        CutsselecTable.push_back(string("At least 2 CSVM Jets"));
        CutsselecTable.push_back(string("At Least 500 GeV HT"));
    }

    SelectionTable selecTable(CutsselecTable, datasets);
    selecTable.SetLuminosity(Luminosity);
    selecTable.SetPrecision(2);

    for(int d = 0; d < datasets.size(); d++) // Loop through datasets
    {
        dataSetName = datasets[d]->Name();
        cout << "Dataset:  :" << dataSetName << endl;
        if(dataSetName.find(otherTTbarsample) != string::npos || dataSetName.find("Scale") != string::npos ||
            dataSetName.find("JES") != string::npos || dataSetName.find("JER") != string::npos|| dataSetName.find("TTJets_aMCatNLO")!=string::npos) {
            continue;
        }

        filepath = CraneenPath + dataSetName + "_Run2_TopTree.root";

        FileObj[dataSetName.c_str()] = new TFile((filepath).c_str()); // create TFile for each dataset
        string nTuplename = "Craneen__" + leptoAbbr + "_CutFlow";
        nTuple[dataSetName.c_str()] = (TNtuple*)FileObj[dataSetName.c_str()]->Get(nTuplename.c_str()); // get ntuple for each dataset
        nEntries = (int)nTuple[dataSetName.c_str()]->GetEntries();
        cout << "                 nEntries: " << nEntries << endl;

        nTuple[dataSetName.c_str()]->SetBranchAddress("isGoodPV", &cuts[1]);
        nTuple[dataSetName.c_str()]->SetBranchAddress("Lep1", &cuts[2]);
        nTuple[dataSetName.c_str()]->SetBranchAddress("Lep2", &cuts[3]);
        nTuple[dataSetName.c_str()]->SetBranchAddress("nJets2", &cuts[4]);
        nTuple[dataSetName.c_str()]->SetBranchAddress("nJets3", &cuts[5]);
        nTuple[dataSetName.c_str()]->SetBranchAddress("nJets4", &cuts[6]);
        nTuple[dataSetName.c_str()]->SetBranchAddress("nTags", &cuts[7]);
        nTuple[dataSetName.c_str()]->SetBranchAddress("HT", &cuts[8]);

        float eqlumi = 1. / datasets[d]->EquivalentLumi();
        cout << "eqlumi: " << eqlumi << endl;
        cout << "got variables" << endl;
        // for fixed bin width

        for(int j = 0; j < nEntries; j++) {
            nTuple[dataSetName.c_str()]->GetEntry(j);
            NormFactor = 1;
            if(dataSetName.find("tttt") != string::npos) {
                NormFactor = 1.0 / 0.4095;
            }
            else if(dataSetName.find("TTJets_aMCatNLO") != string::npos) {
                    NormFactor = 1.0 / 0.3304;
            }
            if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
                dataSetName.find("DATA") != string::npos) {
                selecTable.Fill(d, 0, 1.0);
            } else {
                selecTable.Fill(d, 0, NormFactor * ScaleFactor);
            }

            for(int cutnum = 0; cutnum < nCuts; cutnum++) {
                if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
                    dataSetName.find("DATA") != string::npos) {
                    if(cuts[cutnum] == 1) {
                        cutFlowPlot->Fill(cutnum, datasets[d], true, 1);
                        selecTable.Fill(d, (cutnum + 1), 1);
                    }
                } else {

                    // else if(dataSetName.find("WJets") != string::npos) {
                    //     NormFactor = 1.0/0.522796;
                    // } else if(dataSetName.find("DYJets") != string::npos) {
                    //     NormFactor = 1.0/0.566;
                    // }

                    if(cuts[cutnum] == 1) {
                        cutFlowPlot->Fill(cutnum, datasets[d], true, GenWeight * NormFactor * ScaleFactor * Luminosity);
                        selecTable.Fill(d, (cutnum + 1), GenWeight * NormFactor * ScaleFactor);
                    }
                }
            }
        }
        cout << "after for loop entries" << endl;
    }
    cout << "unloading datasets" << endl;
    cout << "Writing Cut Flow Plot" << endl;
    cutFlowPlot->Draw("Cut Flow", 0, false, true, false, 100);
    cutFlowPlot->Write(cffile, "CutFlow", true, pathPNG, "eps");
    //(bool mergeTT, bool mergeQCD, bool mergeW, bool mergeZ, bool mergeST)
    selecTable.TableCalculator(true, true, true, true, true);

    // Options : WithError (false), writeMerged (true), useBookTabs (false), addRawsyNumbers (false), addEfficiencies
    // (false), addTotalEfficiencies (false), writeLandscape (false)
    selecTable.Write("FourTop" + leptoAbbr + "_Table" + ".tex", false, true, true, true, false, false, true);
}

void SplitDatasetPlotter(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string sSplitVar,
    float fbSplit,
    float ftSplit,
    float fwSplit,
    string xmlNom,
    string CraneenPath,
    string shapefileName,
    string units)
{
    cout << "" << endl;
    cout << "RUNNING NOMINAL DATASETS" << endl;
    cout << "" << endl;
    shapefile->cd();
    errorfile->mkdir(("MultiSamplePlot_" + sVarofinterest).c_str());

    const char* xmlfile = xmlNom.c_str();
    cout << "used config file: " << xmlfile << endl;
    
    float Luminosity;

    string pathPNG = "FourTop_Light";
    pathPNG += leptoAbbr;
    pathPNG += "_MSPlots/";
    mkdir(pathPNG.c_str(), 0777);
    cout << "Making directory :" << pathPNG << endl; // make directory
    string mainTTbarSample;
    string otherTTbarsample;
    string chanText;
    cout << "channel  " << channel << endl;
    if(channel == "ttttmu" || channel == "ttttel") {
        mainTTbarSample = "TTJets_powheg";
        otherTTbarsample = "TTJets_MLM";
    } else {
        mainTTbarSample = "TTJetsPowheg";
        otherTTbarsample = "TTJetsMG";
    }
    if(channel == "ttttmu")
        chanText = "Single Lepton: #mu";
    else if(channel == "ttttel")
        chanText = "Single Lepton: e";
    else if(channel == "ttttmumu"){
        chanText = "Dilepton: #mu#mu ";
        Luminosity = 5743.725979478
                +2573.399420069
                +4248.383597366
                +4009.132398404
                +3101.618412335
                +7540.487735974
                +8390.540446658+215.149415251
                ;
    } else if(channel == "ttttmuel"){
        chanText = "Dilepton: e#mu ";
        Luminosity = 5743.725979478
                +2573.399420069
                +4248.383597366
                +4009.132398404
                +3101.618412335
                +7540.487735974
                +8390.540446658+215.149415251
                ;
    } else if(channel == "ttttelel"){
        chanText = "Dilepton: ee ";
        Luminosity = 5747.595589414
                +2573.399420069
                +4248.383597366
                +4009.132315299
                +3101.618412335
                +7540.487715338
                +8390.540368893+215.149415251
                ;
    } else if(channel == "comb"){
        chanText = "Dilepton: Combined";
        Luminosity = 7540.4877;
    }
    

    ///////////////////////////////////////////////////////////// Load Datasets
    /////////////////////////////////////////////////////////////////////////cout<<"loading...."<<endl;
    TTreeLoader treeLoader;
    vector<Dataset*> datasets;                  // cout<<"vector filled"<<endl;
    treeLoader.LoadDatasets(datasets, xmlfile); // cout<<"datasets loaded"<<endl;

    Dataset* ttbar_ll;
    Dataset* ttbar_ll_up;
    Dataset* ttbar_ll_down;
    Dataset* ttbar_cc;
    Dataset* ttbar_cc_up;
    Dataset* ttbar_cc_down;
    Dataset* ttbar_bb;
    Dataset* ttbar_bb_up;
    Dataset* ttbar_bb_down;

    if(split_ttbar) {
        int ndatasets = datasets.size();
        cout << " - splitting TTBar dataset ..." << ndatasets << endl;
        vector<string> ttbar_filenames = datasets[ndatasets - 1]->Filenames();
        cout << "ttbar filenames =  " << ttbar_filenames[0] << endl;

        ttbar_ll = new Dataset("TTJets_ll", "tt + ll", true, 632, 1, 2, 1, 213.4, ttbar_filenames);
        ttbar_cc = new Dataset("TTJets_cc", "tt + cc", true, 633, 1, 2, 1, 6.9, ttbar_filenames);
        ttbar_bb = new Dataset("TTJets_bb", "tt + bb", true, 634, 1, 2, 1, 4.8, ttbar_filenames);

        int newlumi = 79148.3937674; //datasets[ndatasets - 1]->EquivalentLumi();
        ttbar_ll->SetEquivalentLuminosity(newlumi);
        ttbar_cc->SetEquivalentLuminosity(newlumi);
        ttbar_bb->SetEquivalentLuminosity(newlumi);

        ttbar_ll->SetColor(kRed);
        ttbar_cc->SetColor(kRed - 3);
        ttbar_bb->SetColor(kRed + 2);

        datasets.push_back(ttbar_bb);
        datasets.push_back(ttbar_cc);
        datasets.push_back(ttbar_ll);
    }

    //***************************************************CREATING
    // PLOTS****************************************************
    string plotname; ///// Jet Split plot
    string plotaxis = plotVarNames(sVarofinterest);
    string numStr, numstrplusone;
    string sbSplit = static_cast<ostringstream*>(&(ostringstream() << fbSplit))->str();
    string stSplit = static_cast<ostringstream*>(&(ostringstream() << ftSplit))->str();
    string swSplit = static_cast<ostringstream*>(&(ostringstream() << fwSplit))->str();
    for(int s = fbSplit; s <= ftSplit; s += fwSplit) {
        numStr = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        numstrplusone = static_cast<ostringstream*>(&(ostringstream() << (s+fwSplit-1)))->str();
        plotname = sVarofinterest + numStr + sSplitVar;
        if(s < ftSplit) MSPlot[plotname.c_str()] = new MultiSamplePlot(datasets, plotname.c_str(), nBins, plotLow, plotHigh, plotaxis.c_str(),
                                                                       units, "Events", ( chanText+ " " + numStr + "-" + numstrplusone + " Jets").c_str());
        else MSPlot[plotname.c_str()] = new MultiSamplePlot(datasets, plotname.c_str(), nBins, plotLow, plotHigh, plotaxis.c_str(),
                                                            units, "Events", (chanText+ " " + numStr + "+ Jets").c_str());
        MSPlot[plotname.c_str()]->setPreliminary(prelim_);
        
        histo1D[("TTJets_Rare"+plotname).c_str()] = new TH1F(("TTJets_Rare"+plotname).c_str(), ("TTJets_Rare"+plotname).c_str(), nBins, plotLow, plotHigh);
        //histo1D[("EW" + plotname).c_str()] = new TH1F(("EW" + plotname).c_str(), ("EW" + plotname).c_str(), nBins, plotLow, plotHigh);
    }
    plotname = "";

    //***********************************************OPEN FILES & GET NTUPLES**********************************************
    string dataSetName, filepath, histoName;
    int nEntries;
    float ScaleFactor = 1, NormFactor = 1, varofInterest, splitVar, GenWeight = 1, weight1 = 1, weight2 = 1,
          weight3 = 1, weight4 = 1, weight5 = 1, weight6 = 1, weight7 = 1, weight8 = 1, ttbar_flav = 1, SFtrigger = 1,
          SFlepton = 1, SFbtag_light = 1, SFbtag_lightUp = 1, SFbtag_lightDown = 1, SFbtag_heavy = 1,
          SFbtag_heavyUp = 1, SFbtag_heavyDown = 1, SFPU = 1, SFPU_up = 1, SFPU_down = 1, SFTopPt = 1, SFbehrends = 1,
          nJets = 1, SFalphaTune = 1, SFbtagCSV = 1, btagWeightCSVLFUp = 1, btagWeightCSVLFDown = 1, btagWeightCSVHFUp = 1,
          btagWeightCSVHFDown = 1, btagWeightCSVHFStats1Up = 1, btagWeightCSVHFStats1Down = 1,
          btagWeightCSVHFStats2Up = 1, btagWeightCSVHFStats2Down = 1, btagWeightCSVLFStats1Up = 1,
          btagWeightCSVLFStats1Down = 1, btagWeightCSVLFStats2Up = 1, btagWeightCSVLFStats2Down = 1,
          btagWeightCSVCFErr1Up = 1, btagWeightCSVCFErr1Down = 1, btagWeightCSVCFErr2Up = 1,
          btagWeightCSVCFErr2Down = 1, hdamp_up = 1, hdamp_down = 1, SFtrigger_BCDEF = 1, SFtrigger_GH = 1, SFlepton_BCDEF = 1, SFlepton_GH = 1;
    float PtLepton, ttXrew = 1, ttXrew_up = 1, ttXrew_down = 1, weight_ct10 = 1, weight_mmht14 = 1, HT = 0;

    for(int d = 0; d < datasets.size(); d++) // Loop through datasets
    {
        dataSetName = datasets[d]->Name();
        cout << "Dataset:  :" << dataSetName << endl;
        if(dataSetName.find("TTJets_ll") != string::npos || dataSetName.find("TTJets_cc") != string::npos || dataSetName.find("TTJets_bb") != string::npos) {
            cout << "skip ttbar split datasets!" << endl;
            continue;
        }

        filepath = CraneenPath + dataSetName + "_Run2_TopTree_Study.root";
        // cout<<"filepath: "<<filepath<<endl;

        FileObj[dataSetName.c_str()] = new TFile((filepath).c_str()); // create TFile for each dataset
        string nTuplename = "Craneen__" + leptoAbbr;
        nTuple[dataSetName.c_str()] = (TNtuple*)FileObj[dataSetName.c_str()]->Get(nTuplename.c_str()); // get ntuple for each dataset
        nEntries = (int)nTuple[dataSetName.c_str()]->GetEntries();
        cout << "                 nEntries: " << nEntries << endl;

        if(sVarofinterest.find("nJets") == string::npos) {
            nTuple[dataSetName.c_str()]->SetBranchAddress("nJets", &nJets);
        }
        nTuple[dataSetName.c_str()]->SetBranchAddress(sVarofinterest.c_str(), &varofInterest);
        nTuple[dataSetName.c_str()]->SetBranchAddress("ScaleFactor", &ScaleFactor);
        nTuple[dataSetName.c_str()]->SetBranchAddress("NormFactor", &NormFactor);
        //nTuple[dataSetName.c_str()]->SetBranchAddress("Luminosity", &Luminosity);
        nTuple[dataSetName.c_str()]->SetBranchAddress("hdampup", &hdamp_up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("hdampdown", &hdamp_down);
        nTuple[dataSetName.c_str()]->SetBranchAddress(sSplitVar.c_str(), &splitVar);
        nTuple[dataSetName.c_str()]->SetBranchAddress("GenWeight", &GenWeight);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight1", &weight1);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight2", &weight2);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight3", &weight3);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight4", &weight4);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight5", &weight5);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight6", &weight6);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight7", &weight7);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight8", &weight8);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFleptrig_BCDEF", &SFtrigger_BCDEF);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFleptrig_GH", &SFtrigger_GH);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFlepton_BCDEF", &SFlepton_BCDEF);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFlepton_GH", &SFlepton_GH);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFbtag_light", &SFbtag_light); // SFbtag
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFbtag_lightUp", &SFbtag_lightUp);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFbtag_lightDown", &SFbtag_lightDown);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFbtag_heavy", &SFbtag_heavy); // SFbtag
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFbtag_heavyUp", &SFbtag_heavyUp);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFbtag_heavyDown", &SFbtag_heavyDown);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFPU", &SFPU);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFPU_up", &SFPU_up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFPU_down", &SFPU_down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFtopPt", &SFTopPt); // single lep sfTopPt
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFalphaTune", &SFalphaTune);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFbtagCSV", &SFbtagCSV); // SFbtag
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVLFUp", &btagWeightCSVLFUp);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVLFDown", &btagWeightCSVLFDown);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVHFUp", &btagWeightCSVHFUp);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVHFDown", &btagWeightCSVHFDown);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVHFStats1Up", &btagWeightCSVHFStats1Up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVHFStats1Down", &btagWeightCSVHFStats1Down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVHFStats2Up", &btagWeightCSVHFStats2Up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVHFStats2Down", &btagWeightCSVHFStats2Down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVLFStats1Up", &btagWeightCSVLFStats1Up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVLFStats1Down", &btagWeightCSVLFStats1Down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVLFStats2Up", &btagWeightCSVLFStats2Up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVLFStats2Down", &btagWeightCSVLFStats2Down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVCFErr1Up", &btagWeightCSVCFErr1Up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVCFErr1Down", &btagWeightCSVCFErr1Down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVCFErr2Up", &btagWeightCSVCFErr2Up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVCFErr2Down", &btagWeightCSVCFErr2Down);
        // nTuple[dataSetName.c_str()]->SetBranchAddress("SFbehrends", &SFbehrends);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFtopPt", &SFTopPt);
        // nTuple[dataSetName.c_str()]->SetBranchAddress("ttbar_flav", &ttbar_flav);
        // nTuple[dataSetName.c_str()]->SetBranchAddress("LeptonPt", &PtLepton);
        nTuple[dataSetName.c_str()]->SetBranchAddress("ttXrew", &ttXrew);
        nTuple[dataSetName.c_str()]->SetBranchAddress("ttXrew_up", &ttXrew_up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("ttXrew_down", &ttXrew_down); 

        nTuple[dataSetName.c_str()]->SetBranchAddress("HT", &HT);

        float eqlumi = 1. / datasets[d]->EquivalentLumi();
        cout << "eqlumi: " << eqlumi << endl;

        // for fixed bin width
        for(int s = fbSplit; s <= ftSplit; s += fwSplit) {
            numStr = static_cast<ostringstream*>(&(ostringstream() << s))->str();
            histoName = dataSetName + numStr + sSplitVar;
            histo1D[histoName.c_str()] = new TH1F(histoName.c_str(), histoName.c_str(), nBins, plotLow, plotHigh);

            if(dataSetName.find(mainTTbarSample) != string::npos && dataSetName.find("JES") == string::npos &&
               dataSetName.find("JER") == string::npos && dataSetName.find("ScaleH") == string::npos) {
                histo1D[("Genweight_tt" + numStr).c_str()] = new TH1F(("Genweight_tt" + numStr).c_str(), "Genweight", nBins, plotLow, plotHigh);
                histo1D[("weight1_tt" + numStr).c_str()] = new TH1F(("weight1_tt" + numStr).c_str(), "weight1", nBins, plotLow, plotHigh);
                histo1D[("weight2_tt" + numStr).c_str()] = new TH1F(("weight2_tt" + numStr).c_str(), "weight2", nBins, plotLow, plotHigh);
                histo1D[("weight3_tt" + numStr).c_str()] = new TH1F(("weight3_tt" + numStr).c_str(), "weight3", nBins, plotLow, plotHigh);
                histo1D[("weight4_tt" + numStr).c_str()] = new TH1F(("weight4_tt" + numStr).c_str(), "weight4", nBins, plotLow, plotHigh);
                histo1D[("weight5_tt" + numStr).c_str()] = new TH1F(("weight5_tt" + numStr).c_str(), "weight5", nBins, plotLow, plotHigh);
                histo1D[("weight6_tt" + numStr).c_str()] = new TH1F(("weight6_tt" + numStr).c_str(), "weight6", nBins, plotLow, plotHigh);
                histo1D[("weight7_tt" + numStr).c_str()] = new TH1F(("weight7_tt" + numStr).c_str(), "weight7", nBins, plotLow, plotHigh);
                histo1D[("weight8_tt" + numStr).c_str()] = new TH1F(("weight8_tt" + numStr).c_str(), "weight8", nBins, plotLow, plotHigh);
                histo1D[("PU_Up" + numStr).c_str()] =
			 new TH1F(("PU_Up" + numStr).c_str(), "PU_Up", nBins, plotLow, plotHigh);
                histo1D[("PU_Down" + numStr).c_str()] =
			 new TH1F(("PU_Down" + numStr).c_str(), "PU_Down", nBins, plotLow, plotHigh);
                histo1D[("btag_lightUp" + numStr).c_str()] =
			 new TH1F(("btag_lightUp" + numStr).c_str(), "btag_lightUp", nBins, plotLow, plotHigh);
                histo1D[("btag_lightDown" + numStr).c_str()] =
			 new TH1F(("btag_lightDown" + numStr).c_str(), "btag_lightDown", nBins, plotLow, plotHigh);
                histo1D[("btag_heavyUp" + numStr).c_str()] =
			 new TH1F(("btag_heavyUp" + numStr).c_str(), "btag_heavyUp", nBins, plotLow, plotHigh);
                histo1D[("btag_heavyDown" + numStr).c_str()] =
			 new TH1F(("btag_heavyDown" + numStr).c_str(), "btag_heavyDown", nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVLF_Up"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVLF_Up"+numStr).c_str(), ("btagWeightCSVLF_Up"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVLF_Down"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVLF_Down"+numStr).c_str(), ("btagWeightCSVLF_Down"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVHF_Up"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVHF_Up"+numStr).c_str(), ("btagWeightCSVHF_Up"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVHF_Down"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVHF_Down"+numStr).c_str(), ("btagWeightCSVHF_Down"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVHFStats1_Up"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVHFStats1_Up"+numStr).c_str(), ("btagWeightCSVHFStats1_Up"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVHFStats1_Down"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVHFStats1_Down"+numStr).c_str(), ("btagWeightCSVHFStats1_Down"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVHFStats2_Up"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVHFStats2_Up"+numStr).c_str(), ("btagWeightCSVHFStats2_Up"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVHFStats2_Down"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVHFStats2_Down"+numStr).c_str(), ("btagWeightCSVHFStats2_Down"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVLFStats1_Up"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVLFStats1_Up"+numStr).c_str(), ("btagWeightCSVLFStats1_Up"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVLFStats1_Down"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVLFStats1_Down"+numStr).c_str(), ("btagWeightCSVLFStats1_Down"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVLFStats2_Up"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVLFStats2_Up"+numStr).c_str(), ("btagWeightCSVLFStats2_Up"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVLFStats2_Down"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVLFStats2_Down"+numStr).c_str(), ("btagWeightCSVLFStats2_Down"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVCFErr1_Up"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVCFErr1_Up"+numStr).c_str(), ("btagWeightCSVCFErr1_Up"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVCFErr1_Down"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVCFErr1_Down"+numStr).c_str(), ("btagWeightCSVCFErr1_Down"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVCFErr2_Up"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVCFErr2_Up"+numStr).c_str(), ("btagWeightCSVCFErr2_Up"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVCFErr2_Down"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVCFErr2_Down"+numStr).c_str(), ("btagWeightCSVCFErr2_Down"+numStr).c_str(), nBins, plotLow, plotHigh);  
                histo1D[("heavyFlav_Up" + numStr).c_str()] = new TH1F(("heavyFlav_Up" + numStr).c_str(), "heavyFlav_Up", nBins, plotLow, plotHigh);
                histo1D[("heavyFlav_Down" + numStr).c_str()] = new TH1F(("heavyFlav_Down" + numStr).c_str(), "heavyFlav_Down", nBins, plotLow, plotHigh);
                histo1D[("hdamp_Up" + numStr).c_str()] = new TH1F(("hdamp_Up" + numStr).c_str(), "hdamp_Up", nBins, plotLow, plotHigh);
                histo1D[("hdamp_Down" + numStr).c_str()] = new TH1F(("hdamp_Down" + numStr).c_str(), "hdamp_Down", nBins, plotLow, plotHigh);
                histo1D[("TTJetsPDF_Up" + numStr).c_str()] = new TH1F(("TTJetsPDF_Up" + numStr).c_str(), "TTJetsPDF_Up", nBins, plotLow, plotHigh);
                histo1D[("TTJetsPDF_Down" + numStr).c_str()] = new TH1F(("TTJetsPDF_Down" + numStr).c_str(), "TTJetsPDF_Down", nBins, plotLow, plotHigh);

            } else if(dataSetName.find("tttt") != string::npos && dataSetName.find("JES") == string::npos &&
                      dataSetName.find("JER") == string::npos && dataSetName.find("ScaleH") == string::npos) {
                histo1D[("Genweight_tttt" + numStr).c_str()] = new TH1F(("Genweight_tttt" + numStr).c_str(), "Genweight_tttt", nBins, plotLow, plotHigh);
                histo1D[("weight1_tttt" + numStr).c_str()] = new TH1F(("weight1_tttt" + numStr).c_str(), "weight1_tttt", nBins, plotLow, plotHigh);
                histo1D[("weight2_tttt" + numStr).c_str()] = new TH1F(("weight2_tttt" + numStr).c_str(), "weight2_tttt", nBins, plotLow, plotHigh);
                histo1D[("weight3_tttt" + numStr).c_str()] = new TH1F(("weight3_tttt" + numStr).c_str(), "weight3_tttt", nBins, plotLow, plotHigh);
                histo1D[("weight4_tttt" + numStr).c_str()] = new TH1F(("weight4_tttt" + numStr).c_str(), "weight4_tttt", nBins, plotLow, plotHigh);
                histo1D[("weight5_tttt" + numStr).c_str()] = new TH1F(("weight5_tttt" + numStr).c_str(), "weight5_tttt", nBins, plotLow, plotHigh);
                histo1D[("weight6_tttt" + numStr).c_str()] = new TH1F(("weight6_tttt" + numStr).c_str(), "weight6_tttt", nBins, plotLow, plotHigh);
                histo1D[("weight7_tttt" + numStr).c_str()] = new TH1F(("weight7_tttt" + numStr).c_str(), "weight7_tttt", nBins, plotLow, plotHigh);
                histo1D[("weight8_tttt" + numStr).c_str()] = new TH1F(("weight8_tttt" + numStr).c_str(), "weight8_tttt", nBins, plotLow, plotHigh);
                histo1D[("PU_Up_tttt" + numStr).c_str()] =
			 new TH1F(("PU_Up_tttt" + numStr).c_str(), "PU_Up_tttt", nBins, plotLow, plotHigh);
                histo1D[("PU_Down_tttt" + numStr).c_str()] =
			 new TH1F(("PU_Down_tttt" + numStr).c_str(), "PU_Down_tttt", nBins, plotLow, plotHigh);
                histo1D[("btag_lightUp_tttt" + numStr).c_str()] =
			 new TH1F(("btag_lightUp_tttt" + numStr).c_str(), "btag_lightUp_tttt", nBins, plotLow, plotHigh);
                histo1D[("btag_lightDown_tttt" + numStr).c_str()] =
			 new TH1F(("btag_lightDown_tttt" + numStr).c_str(), "btag_lightDown_tttt", nBins, plotLow, plotHigh);
                histo1D[("btag_heavyUp_tttt" + numStr).c_str()] =
			 new TH1F(("btag_heavyUp_tttt" + numStr).c_str(), "btag_heavyUp_tttt", nBins, plotLow, plotHigh);
                histo1D[("btag_heavyDown_tttt" + numStr).c_str()] =
			 new TH1F(("btag_heavyDown_tttt" + numStr).c_str(), "btag_heavyDown_tttt", nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVLF_Up_tttt"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVLF_Up_tttt"+numStr).c_str(), ("btagWeightCSVLF_Up_tttt"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVLF_Down_tttt"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVLF_Down_tttt"+numStr).c_str(), ("btagWeightCSVLF_Down_tttt"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVHF_Up_tttt"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVHF_Up_tttt"+numStr).c_str(), ("btagWeightCSVHF_Up_tttt"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVHF_Down_tttt"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVHF_Down_tttt"+numStr).c_str(), ("btagWeightCSVHF_Down_tttt"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVHFStats1_Up_tttt"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVHFStats1_Up_tttt"+numStr).c_str(), ("btagWeightCSVHFStats1_Up_tttt"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVHFStats1_Down_tttt"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVHFStats1_Down_tttt"+numStr).c_str(), ("btagWeightCSVHFStats1_Down_tttt"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVHFStats2_Up_tttt"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVHFStats2_Up_tttt"+numStr).c_str(), ("btagWeightCSVHFStats2_Up_tttt"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVHFStats2_Down_tttt"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVHFStats2_Down_tttt"+numStr).c_str(), ("btagWeightCSVHFStats2_Down_tttt"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVLFStats1_Up_tttt"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVLFStats1_Up_tttt"+numStr).c_str(), ("btagWeightCSVLFStats1_Up_tttt"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVLFStats1_Down_tttt"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVLFStats1_Down_tttt"+numStr).c_str(), ("btagWeightCSVLFStats1_Down_tttt"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVLFStats2_Up_tttt"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVLFStats2_Up_tttt"+numStr).c_str(), ("btagWeightCSVLFStats2_Up_tttt"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVLFStats2_Down_tttt"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVLFStats2_Down_tttt"+numStr).c_str(), ("btagWeightCSVLFStats2_Down_tttt"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVCFErr1_Up_tttt"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVCFErr1_Up_tttt"+numStr).c_str(), ("btagWeightCSVCFErr1_Up_tttt"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVCFErr1_Down_tttt"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVCFErr1_Down_tttt"+numStr).c_str(), ("btagWeightCSVCFErr1_Down_tttt"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVCFErr2_Up_tttt"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVCFErr2_Up_tttt"+numStr).c_str(), ("btagWeightCSVCFErr2_Up_tttt"+numStr).c_str(), nBins, plotLow, plotHigh);
                histo1D[("btagWeightCSVCFErr2_Down_tttt"+numStr).c_str()] =
			 new TH1F(("btagWeightCSVCFErr2_Down_tttt"+numStr).c_str(), ("btagWeightCSVCFErr2_Down_tttt"+numStr).c_str(), nBins, plotLow, plotHigh);                    
            }

        }
        /////*****loop through entries and fill plots*****

        //Luminosity = 24325.9;

        float ProjectedLumi = 10000; // pb-1
        float LumiFactor = 1;
        // float LumiFactor = ProjectedLumi/Luminosity;

        for(int j = 0; j < nEntries; j++) {
            nTuple[dataSetName.c_str()]->GetEntry(j);

            // if(HT<525) continue;

            // artificial Lumi
            // if(lScale > 0 )
            // {
            //     Luminosity = 1000*lScale;
            // }

            NormFactor = 1;
            // SFTopPt = 1;
            SFbehrends = 1;
            SFalphaTune = 1;
            SFtrigger = (19676.2598077*SFtrigger_BCDEF + 16146.1775979*SFtrigger_GH)/(35822.4374055);
            SFlepton = (19676.2598077*SFlepton_BCDEF + 16146.1775979*SFlepton_GH)/(35822.4374055);

            //Inflating btagging systematics by a factor of 2
            float SFbtag_lightUpInflated = SFbtag_light + 4*(SFbtag_lightUp - SFbtag_light);
            float SFbtag_lightDownInflated = SFbtag_light - 4*(SFbtag_light - SFbtag_lightDown);
            float SFbtag_heavyUpInflated = SFbtag_heavy + 4*(SFbtag_heavyUp - SFbtag_heavy);
            float SFbtag_heavyDownInflated = SFbtag_heavy - 4*(SFbtag_heavy - SFbtag_heavyDown);

            //SFbtag_heavy = SFbtagCSV;
            //SFbtag_light = 1.0;

            if(dataSetName.find("tttt") != string::npos) {
                NormFactor = 1.0 / 0.4168;
            } else if(dataSetName.find("TTW") != string::npos) {
                NormFactor = 1.0 / 0.5151;
            } else if(dataSetName.find("TTZ") != string::npos) {
                NormFactor = 1.0 / 0.4658;
            } else if(dataSetName.find("TTJets_aMCatNLO") != string::npos) {
                NormFactor = 1.0 / 0.3304;
            }
            // else if(dataSetName.find("WJets") != string::npos) {
            //     NormFactor = 1.0/0.522796;
            // } else if(dataSetName.find("DYJets") != string::npos) {
            //     NormFactor = 1.0/0.566;
            // }

            float ttbbReweight = 1, ttbbReweight_up = 1, ttbbReweight_down = 1;
            if(reweight_ttbar && dataSetName.find("TTJets") != string::npos) {
                ttbbReweight = ttXrew;
                ttbbReweight_up = ttXrew_up;
                ttbbReweight_down = ttXrew_down;
            }

            if(splitVar >= ftSplit) // Check if this entry belongs in the last bin.  Done here to optimize number of checks
            {
                plotname = sVarofinterest + stSplit + sSplitVar;
                histoName = dataSetName + stSplit + sSplitVar;
                // cout << "Last Bin Event! SplitVar = " << splitVar << endl;

                if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos || dataSetName.find("DATA") != string::npos || dataSetName.find("NP_overlay_Data") != string::npos) {
                    ////////DATA BLINDED ////
                    // if(sVarofinterest.find("BDT") == string::npos)
                    MSPlot[plotname]->Fill(varofInterest, datasets[d], true, 1);
                    // MSPlot[plotname]->Fill(varofInterest, datasets[d], true, LumiFactor);
                    histo1D[histoName.c_str()]->Fill(varofInterest, eqlumi * LumiFactor);
                }
                // outsiderange = false;
                else if(dataSetName.find(mainTTbarSample) != string::npos && dataSetName.find("JES") == string::npos && dataSetName.find("JER") == string::npos && dataSetName.find("ScaleH") == string::npos) {
                    // cout << "Main TTbar Sample Event!  stSplit = " << stSplit << endl;
                    //                    cin.get();
                    
                    histo1D[("Genweight_tt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight *
                            LumiFactor * GenWeight);
                    histo1D[("weight1_tt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight *
                            LumiFactor * weight1);
                    histo1D[("weight2_tt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight *
                            LumiFactor * weight2);
                    histo1D[("weight3_tt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight *
                            LumiFactor * weight3);
                    histo1D[("weight4_tt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight *
                            LumiFactor * weight4);
                    histo1D[("weight5_tt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight *
                            LumiFactor * weight5);
                    histo1D[("weight6_tt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight *
                            LumiFactor * weight6);
                    histo1D[("weight7_tt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight *
                            LumiFactor * weight7);
                    histo1D[("weight8_tt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight *
                            LumiFactor * weight8);
                    histo1D[("PU_Up" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU_up * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight *
                            LumiFactor * GenWeight);
                    histo1D[("PU_Down" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU_down * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight *
                            LumiFactor * GenWeight);
                    histo1D[("btag_lightUp" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtag_lightUpInflated * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight *
                            LumiFactor * GenWeight);
                    histo1D[("btag_lightDown" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtag_lightDownInflated * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight *
                            LumiFactor * GenWeight);
                    histo1D[("btag_heavyUp" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtag_heavyUpInflated * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight *
                            LumiFactor * GenWeight);
                    histo1D[("btag_heavyDown" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtag_heavyDownInflated * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight *
                            LumiFactor * GenWeight);
                    histo1D[("btagWeightCSVLF_Up"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            btagWeightCSVLFUp * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                            ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVLF_Down"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            btagWeightCSVLFDown * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                            ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVHF_Up"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            btagWeightCSVHFUp * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                            ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVHF_Down"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            btagWeightCSVHFDown * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                            ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVHFStats1_Up"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            btagWeightCSVHFStats1Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                            ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVHFStats1_Down"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            btagWeightCSVHFStats1Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                            ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVHFStats2_Up"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            btagWeightCSVHFStats2Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                            ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVHFStats2_Down"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            btagWeightCSVHFStats2Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                            ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVLFStats1_Up"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            btagWeightCSVLFStats1Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                            ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVLFStats1_Down"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            btagWeightCSVLFStats1Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                            ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVLFStats2_Up"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            btagWeightCSVLFStats2Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                            ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVLFStats2_Down"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            btagWeightCSVLFStats2Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                            ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVCFErr1_Up"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            btagWeightCSVCFErr1Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                            ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVCFErr1_Down"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            btagWeightCSVCFErr1Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                            ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVCFErr2_Up"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            btagWeightCSVCFErr2Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                            ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVCFErr2_Down"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            btagWeightCSVCFErr2Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                            ttbbReweight * LumiFactor);
                    histo1D[("heavyFlav_Up" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight_up *
                            LumiFactor * GenWeight);
                    histo1D[("heavyFlav_Down" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight_down *
                            LumiFactor * GenWeight);
                    histo1D[("hdamp_Up" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            hdamp_up * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight *
                            LumiFactor * GenWeight);
                    histo1D[("hdamp_Down" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            hdamp_down * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight *
                            LumiFactor * GenWeight);
                    histo1D[("TTJetsPDF_Up" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                            ttbbReweight * LumiFactor * findmax(weight_ct10, weight_mmht14, (float) 1.0));
                    histo1D[("TTJetsPDF_Down" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                            ttbbReweight * LumiFactor * findmin(weight_ct10, weight_mmht14, (float) 1.0));

                    histo1D[histoName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                            SFPU * SFTopPt * SFbehrends * GenWeight * Luminosity * eqlumi * ttbbReweight);
                    if(split_ttbar) {
                        if(ttXrew < 1) {
                            MSPlot[plotname]->Fill(varofInterest, ttbar_ll, true, NormFactor * GenWeight * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor);
                        } else if(ttXrew > 1) {
                            MSPlot[plotname]->Fill(varofInterest, ttbar_bb, true, NormFactor * GenWeight * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor);
                        } else {
                            MSPlot[plotname]->Fill(varofInterest, ttbar_cc, true, NormFactor * GenWeight * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor);
                        }
                    } else {
                        MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * GenWeight * SFtrigger * SFlepton *
                            SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor);
                    }
                } else if(dataSetName.find("NP_overlay_tttt") != string::npos && dataSetName.find("Scale") == string::npos &&
                          dataSetName.find("JES") == string::npos && dataSetName.find("JER") == string::npos) {
                    histo1D[("Genweight_tttt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                    histo1D[("weight1_tttt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight1);
                    histo1D[("weight2_tttt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight2);
                    histo1D[("weight3_tttt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight3);
                    histo1D[("weight4_tttt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight4);
                    histo1D[("weight5_tttt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight5);
                    histo1D[("weight6_tttt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight6);
                    histo1D[("weight7_tttt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight7);
                    histo1D[("weight8_tttt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight8);
                    histo1D[("PU_Up_tttt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU_up * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                    histo1D[("PU_Down_tttt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU_down * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                    histo1D[("btag_lightUp_tttt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtag_lightUpInflated * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                    histo1D[("btag_lightDown_tttt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtag_lightDownInflated * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                    histo1D[("btag_heavyUp_tttt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtag_heavyUpInflated * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                    histo1D[("btag_heavyDown_tttt" + stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtag_heavyDownInflated * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                    histo1D[("btagWeightCSVLF_Up_tttt"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFUp * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVLF_Down_tttt"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFDown * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVHF_Up_tttt"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFUp * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVHF_Down_tttt"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFDown * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVHFStats1_Up_tttt"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats1Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVHFStats1_Down_tttt"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats1Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVHFStats2_Up_tttt"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats2Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVHFStats2_Down_tttt"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats2Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVLFStats1_Up_tttt"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats1Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVLFStats1_Down_tttt"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats1Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVLFStats2_Up_tttt"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats2Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVLFStats2_Down_tttt"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats2Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVCFErr1_Up_tttt"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr1Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVCFErr1_Down_tttt"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr1Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVCFErr2_Up_tttt"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr2Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    histo1D[("btagWeightCSVCFErr2_Down_tttt"+stSplit).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr2Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);

                    MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor * GenWeight);
                    histo1D[histoName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * GenWeight * Luminosity * eqlumi * ttbbReweight);
                    // cout<<dataSetName<<" "<<varofInterest<<"  "<<NormFactor<<"  "<<SFlepton<<"  "<<SFbtag<<"
                    // "<<SFPU<<"  "<<Luminosity<<"  "<<ttbbReweight<<"  "<<LumiFactor<<"  "<<GenWeight<<endl;
                } else if(dataSetName.find("TTZ") != string::npos || dataSetName.find("TTW") != string::npos ||
                          dataSetName.find("TTH") != string::npos || dataSetName.find("TTJets_SingleLept") != string::npos) {
                    histo1D["TTJets_Rare" + plotname]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                        SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                    MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                        SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor * GenWeight);
                } else if(dataSetName.find(otherTTbarsample) == string::npos && dataSetName.find("TTJets_aMCatNLO")==string::npos && 
                          dataSetName.find("Scale") == string::npos && dataSetName.find("JES") == string::npos &&
                          dataSetName.find("JER") == string::npos && dataSetName.find("TTUE") == string::npos &&
                          dataSetName.find("ISR") == string::npos && dataSetName.find("FSR") == string::npos) { 
                    // ie. don't add the MLM dataset which is just used for ttGenerator
                    MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                            SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor * GenWeight);
                    histo1D[histoName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU *
                            SFTopPt * SFbehrends * GenWeight * Luminosity * eqlumi * ttbbReweight);
                } else {
                    histo1D[histoName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU *
                            SFTopPt * SFbehrends * GenWeight * Luminosity * eqlumi * ttbbReweight);
                }
            } else { 
                // If it doesn't belong in the last bin, find out which it belongs in
                bool outsiderange = true;
                for(int s = fbSplit; s <= ftSplit; s += fwSplit) {
                    if(splitVar >= s && splitVar < (s + fwSplit)) // splitVar falls inside one of the bins
                    {
                        numStr = static_cast<ostringstream*>(&(ostringstream() << s))->str();
                        plotname = sVarofinterest + numStr + sSplitVar;
                        histoName = dataSetName + numStr + sSplitVar;

                        if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
                           dataSetName.find("DATA") != string::npos || dataSetName.find("NP_overlay_Data") != string::npos) {
                            ////////DATA BLINDED ////
                            // if(sVarofinterest.find("BDT") == string::npos)
                            MSPlot[plotname]->Fill(varofInterest, datasets[d], true, 1);
                            histo1D[histoName.c_str()]->Fill(varofInterest, eqlumi * LumiFactor);
                        } else if(dataSetName == mainTTbarSample && dataSetName.find("JES") == string::npos &&
                                  dataSetName.find("JER") == string::npos  && dataSetName.find("ScaleH") == string::npos) {
                            histo1D[("Genweight_tt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                            histo1D[("weight1_tt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight1);
                            histo1D[("weight2_tt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight2);
                            histo1D[("weight3_tt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight3);
                            histo1D[("weight4_tt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight4);
                            histo1D[("weight5_tt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight5);
                            histo1D[("weight6_tt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight6);
                            histo1D[("weight7_tt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight7);
                            histo1D[("weight8_tt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight8);
                            histo1D[("PU_Up" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU_up * SFTopPt * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                            histo1D[("PU_Down" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU_down * SFTopPt * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                            histo1D[("btag_lightUp" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtag_lightUpInflated * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                            histo1D[("btag_lightDown" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtag_lightDownInflated * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                            histo1D[("btag_heavyUp" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtag_heavyUpInflated * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                            histo1D[("btag_heavyDown" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtag_heavyDownInflated * SFalphaTune * SFPU * SFTopPt *SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                            histo1D[("heavyFlav_Up" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight_up * LumiFactor * GenWeight);
                            histo1D[("heavyFlav_Down" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight_down * LumiFactor * GenWeight);
                            histo1D[("hdamp_Up" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * hdamp_up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                            histo1D[("hdamp_Down" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * hdamp_down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                            histo1D[("btagWeightCSVLF_Up"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFUp * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVLF_Down"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFDown * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVHF_Up"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFUp * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVHF_Down"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFDown * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVHFStats1_Up"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats1Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVHFStats1_Down"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats1Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVHFStats2_Up"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats2Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVHFStats2_Down"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats2Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVLFStats1_Up"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats1Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVLFStats1_Down"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats1Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVLFStats2_Up"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats2Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVLFStats2_Down"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats2Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVCFErr1_Up"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr1Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVCFErr1_Down"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr1Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVCFErr2_Up"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr2Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVCFErr2_Down"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr2Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);

                            histo1D[("TTJetsPDF_Up" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                                    SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                                    ttbbReweight * LumiFactor * findmax(weight_ct10, weight_mmht14, (float) 1.0));
                            histo1D[("TTJetsPDF_Down" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                                    SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                                    ttbbReweight * LumiFactor * findmin(weight_ct10, weight_mmht14, (float) 1.0));

                            histo1D[histoName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV *
                                    SFalphaTune * SFPU * SFTopPt * SFbehrends * GenWeight * Luminosity * eqlumi * ttbbReweight);

                            if(split_ttbar) {
                                if(ttXrew < 1) {
                                    MSPlot[plotname]->Fill(varofInterest, ttbar_ll, true, NormFactor * GenWeight * SFtrigger * SFlepton *
                                    SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor);
                                } else if(ttXrew > 1) {
                                    MSPlot[plotname]->Fill(varofInterest, ttbar_bb, true, NormFactor * GenWeight * SFtrigger * SFlepton *
                                    SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor);
                                } else {
                                    MSPlot[plotname]->Fill(varofInterest, ttbar_cc, true, NormFactor * GenWeight * SFtrigger * SFlepton *
                                    SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor);
                                }
                            } else {
                                MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * GenWeight * SFtrigger * SFlepton *
                                    SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor);
                            }
                        } else if(dataSetName.find("NP_overlay_tttt") != string::npos && dataSetName.find("Scale") == string::npos && dataSetName.find("JES") == string::npos && dataSetName.find("JER") == string::npos) { // ie. don't add the MLM dataset which is just used for ttGenerator
                            histo1D[("Genweight_tttt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                            histo1D[("weight1_tttt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight1);
                            histo1D[("weight2_tttt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight2);
                            histo1D[("weight3_tttt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight3);
                            histo1D[("weight4_tttt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight4);
                            histo1D[("weight5_tttt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight5);
                            histo1D[("weight6_tttt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight6);
                            histo1D[("weight7_tttt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight7);
                            histo1D[("weight8_tttt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * weight8);
                            histo1D[("PU_Up_tttt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU_up * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                            histo1D[("PU_Down_tttt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU_down * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                            histo1D[("btag_lightUp_tttt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtag_lightUpInflated * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                            histo1D[("btag_lightDown_tttt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtag_lightDownInflated * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                            histo1D[("btag_heavyUp_tttt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtag_heavyUpInflated * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
                            histo1D[("btag_heavyDown_tttt" + numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtag_heavyDownInflated * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi * ttbbReweight * LumiFactor * GenWeight);
	                    histo1D[("btagWeightCSVLF_Up_tttt"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFUp * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVLF_Down_tttt"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFDown * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVHF_Up_tttt"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFUp * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor); 
                            histo1D[("btagWeightCSVHF_Down_tttt"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFDown * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVHFStats1_Up_tttt"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats1Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVHFStats1_Down_tttt"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats1Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVHFStats2_Up_tttt"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats2Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVHFStats2_Down_tttt"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVHFStats2Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVLFStats1_Up_tttt"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats1Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVLFStats1_Down_tttt"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats1Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVLFStats2_Up_tttt"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats2Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVLFStats2_Down_tttt"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVLFStats2Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVCFErr1_Up_tttt"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr1Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVCFErr1_Down_tttt"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr1Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVCFErr2_Up_tttt"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr2Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
	                    histo1D[("btagWeightCSVCFErr2_Down_tttt"+numStr).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * btagWeightCSVCFErr2Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);

                            MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor * GenWeight);
                            histo1D[histoName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * GenWeight * Luminosity * eqlumi * ttbbReweight);
                        } else if(dataSetName.find("TTZ") != string::npos || dataSetName.find("TTW") != string::npos ||
                                 dataSetName.find("TTH") != string::npos || dataSetName.find("TTJets_SingleLept") != string::npos) {
                            MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * SFtrigger * SFlepton * SFbtagCSV *
                                SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor * GenWeight);
                            histo1D["TTJets_Rare" + plotname]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV *
                                SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi * ttbbReweight * LumiFactor);
                        } else if(dataSetName.find(otherTTbarsample) == string::npos && dataSetName.find("TTJets_aMCatNLO")==string::npos &&
                                  dataSetName.find("Scale") == string::npos && dataSetName.find("JES") == string::npos &&
                                  dataSetName.find("JER") == string::npos && dataSetName.find("TTUE") == string::npos &&
                                  dataSetName.find("ISR") == string::npos && dataSetName.find("FSR") == string::npos) { 
                            // ie. don't add the MLM dataset which is just used for ttGenerator
                            MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                                    SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * LumiFactor * GenWeight);
                            histo1D[histoName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt *
                                    SFbehrends * GenWeight * Luminosity * eqlumi * ttbbReweight);
                        } else {
                            histo1D[histoName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt *
                                    SFbehrends * GenWeight * Luminosity * eqlumi * ttbbReweight);
                        }

                        outsiderange = false;
                        break;
                    }
                }

                if(outsiderange == true) {
                    continue;
                }
            }
        } // end of entries for loop

        shapefile->cd();
        TCanvas* canv = new TCanvas();
        for(int s = fbSplit; s <= ftSplit; s += fwSplit) {
            numStr = static_cast<ostringstream*>(&(ostringstream() << s))->str();
            plotname = sVarofinterest + numStr + sSplitVar;
            histoName = dataSetName + numStr + sSplitVar;
            histo1D[histoName.c_str()]->Draw();
            string writename = "";
            if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos || dataSetName.find("DATA") != string::npos) {
                writename = channel + numStr + sSplitVar + "__data_obs__nominal";
            } else if(dataSetName.find("JESUp") != string::npos && dataSetName.find(mainTTbarSample) != string::npos) {
                writename = channel + numStr + sSplitVar + "__" +"TTJetsPowheg" + "__JESUp";
            } else if(dataSetName.find("JESDown") != string::npos && dataSetName.find(mainTTbarSample) != string::npos) {
                writename = channel + numStr + sSplitVar + "__" +"TTJetsPowheg" + "__JESDown";
            } else if(dataSetName.find("JERUp") != string::npos && dataSetName.find(mainTTbarSample) != string::npos) {
                writename = channel + numStr + sSplitVar + "__" +"TTJetsPowheg" + "__JERUp";
            } else if(dataSetName.find("JERDown") != string::npos && dataSetName.find(mainTTbarSample) != string::npos) {
                writename = channel + numStr + sSplitVar + "__" +"TTJetsPowheg" + "__JERDown";
            } else if(dataSetName.find("TTUEUp") != string::npos) {
                writename = channel + numStr + sSplitVar + "__" +"TTJetsPowheg" + "__TTUEUp";
            } else if(dataSetName.find("TTUEDown") != string::npos) {
                writename = channel + numStr + sSplitVar + "__" +"TTJetsPowheg" + "__TTUEDown";
            } else if(dataSetName.find("TTISRUp") != string::npos){
                writename = channel + numStr + sSplitVar + "__" +"TTJetsPowheg" + "__TTISRUp";
            } else if(dataSetName.find("TTISRDown") != string::npos){
                writename = channel + numStr + sSplitVar + "__" +"TTJetsPowheg" + "__TTISRDown";
            } else if(dataSetName.find("TTFSRUp") != string::npos){
                writename = channel + numStr + sSplitVar + "__" +"TTJetsPowheg" + "__TTFSRUp";
            } else if(dataSetName.find("TTFSRDown") != string::npos){
                writename = channel + numStr + sSplitVar + "__" +"TTJetsPowheg" + "__TTFSRDown";
            } else if(dataSetName.find("ttttISRUp") != string::npos){
                writename = channel + numStr + sSplitVar + "__" + "NP_overlay_ttttNLO" + "__ttttISRUp";
            } else if(dataSetName.find("ttttISRDown") != string::npos){
                writename = channel + numStr + sSplitVar + "__" + "NP_overlay_ttttNLO" + "__ttttISRDown";
            } else if(dataSetName.find("ttttFSRUp") != string::npos){
                writename = channel + numStr + sSplitVar + "__" + "NP_overlay_ttttNLO" + "__ttttFSRUp";
            } else if(dataSetName.find("ttttFSRDown") != string::npos){
                writename = channel + numStr + sSplitVar + "__" + "NP_overlay_ttttNLO" + "__ttttFSRDown";
            } else if(dataSetName.find("JESUp") != string::npos && dataSetName.find("tttt") != string::npos) {
                writename = channel + numStr + sSplitVar + "__" + "NP_overlay_ttttNLO" + "__JESUp";
            } else if(dataSetName.find("JESDown") != string::npos && dataSetName.find("tttt") != string::npos) {
                writename = channel + numStr + sSplitVar + "__" + "NP_overlay_ttttNLO" + "__JESDown";
            } else if(dataSetName.find("JERUp") != string::npos && dataSetName.find("tttt") != string::npos) {
                writename = channel + numStr + sSplitVar + "__" + "NP_overlay_ttttNLO" + "__JERUp";
            } else if(dataSetName.find("JERDown") != string::npos && dataSetName.find("tttt") != string::npos) {
                writename = channel + numStr + sSplitVar + "__" + "NP_overlay_ttttNLO" + "__JERDown";
            } else {
                writename = channel + numStr + sSplitVar + "__" + dataSetName + "__nominal";
            }
            // cout<<"writename  :"<<writename<<endl;
            histo1D[histoName.c_str()]->Write((writename).c_str());

            canv->SaveAs((pathPNG + histoName + ".png").c_str());
            if(dataSetName.find(mainTTbarSample) != string::npos && dataSetName.find("JES") == string::npos &&
               dataSetName.find("JER") == string::npos && dataSetName.find("ScaleH") == string::npos) {
                cout << "  making weights histos" << endl;

                // TCanvas *canv0 = new TCanvas();
                // histo1D[("Genweight_tt"+numStr).c_str()]->Draw();
                histo1D[("Genweight_tt" + numStr).c_str()]->Write(("Genweight_tt" + numStr).c_str());
                // canv0->SaveAs(("Genweight_tt"+numStr+".png").c_str());

                for(int ii = 1; ii < 9; ii++) {
                    // TCanvas *canv1 = new TCanvas();
                    string weightstring = static_cast<ostringstream*>(&(ostringstream() << ii))->str();
                    string weighthisto = "weight" + weightstring + "_tt" + numStr;
                    // histo1D[weighthisto]->Draw();
                    histo1D[weighthisto]->Write(("weight" + weightstring + "_tt" + numStr).c_str());
                    // canv1->SaveAs(("weight"+weightstring+"_tt"+numStr+".png").c_str());
                }
                string MEScalesysname = channel + numStr + sSplitVar + "__" + "TTJetsPowheg" + "__";

                histo1D[("PU_Up" + numStr).c_str()]->Write((MEScalesysname + "PUUp").c_str());
                histo1D[("PU_Down" + numStr).c_str()]->Write((MEScalesysname + "PUDown").c_str());
                histo1D[("btag_lightUp" + numStr).c_str()]->Write((MEScalesysname + "btag_lightUp").c_str());
                histo1D[("btag_lightDown" + numStr).c_str()]->Write((MEScalesysname + "btag_lightDown").c_str());
                histo1D[("btag_heavyUp" + numStr).c_str()]->Write((MEScalesysname + "btag_heavyUp").c_str());
                histo1D[("btag_heavyDown" + numStr).c_str()]->Write((MEScalesysname + "btag_heavyDown").c_str());
                histo1D[("heavyFlav_Up" + numStr).c_str()]->Write((MEScalesysname + "heavyFlavUp").c_str());
                histo1D[("heavyFlav_Down" + numStr).c_str()]->Write((MEScalesysname + "heavyFlavDown").c_str());
                histo1D[("hdamp_Up" + numStr).c_str()]->Write((MEScalesysname + "TTJets_HDAMPUp").c_str());
                histo1D[("hdamp_Down" + numStr).c_str()]->Write((MEScalesysname + "TTJets_HDAMPDown").c_str());
                histo1D[("TTJetsPDF_Up" + numStr).c_str()]->Write((MEScalesysname + "TTJets_PDFUp").c_str());
                histo1D[("TTJetsPDF_Down" + numStr).c_str()]->Write((MEScalesysname + "TTJets_PDFDown").c_str());
                histo1D[("btagWeightCSVLF_Up" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVLFUp").c_str());
                histo1D[("btagWeightCSVLF_Down" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVLFDown").c_str());
                histo1D[("btagWeightCSVHF_Up" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVHFUp").c_str());
                histo1D[("btagWeightCSVHF_Down" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVHFDown").c_str());
                histo1D[("btagWeightCSVHFStats1_Up" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats1Up").c_str());
                histo1D[("btagWeightCSVHFStats1_Down" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats1Down").c_str());
                histo1D[("btagWeightCSVHFStats2_Up" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats2Up").c_str());
                histo1D[("btagWeightCSVHFStats2_Down" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats2Down").c_str());
                histo1D[("btagWeightCSVLFStats1_Up" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats1Up").c_str());
                histo1D[("btagWeightCSVLFStats1_Down" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats1Down").c_str());
                histo1D[("btagWeightCSVLFStats2_Up" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats2Up").c_str());
                histo1D[("btagWeightCSVLFStats2_Down" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats2Down").c_str());
                histo1D[("btagWeightCSVCFErr1_Up" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr1Up").c_str());
                histo1D[("btagWeightCSVCFErr1_Down" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr1Down").c_str());
                histo1D[("btagWeightCSVCFErr2_Up" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr2Up").c_str());
                histo1D[("btagWeightCSVCFErr2_Down" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr2Down").c_str());
                MSPlot[plotname.c_str()]->setDataLumi(Luminosity);
            }
            if(dataSetName.find("NP_overlay_tttt") != string::npos && dataSetName.find("JES") == string::npos &&
               dataSetName.find("JER") == string::npos && dataSetName.find("ScaleH") == string::npos) {
                cout << "  making weights histos" << endl;

                // TCanvas *canv0 = new TCanvas();
                // histo1D[("Genweight_tt"+numStr).c_str()]->Draw();
                histo1D[("Genweight_tttt" + numStr).c_str()]->Write(("Genweight_tttt" + numStr).c_str());
                // canv0->SaveAs(("Genweight_tt"+numStr+".png").c_str());

                for(int ii = 1; ii < 9; ii++) {
                    // TCanvas *canv1 = new TCanvas();
                    string weightstring = static_cast<ostringstream*>(&(ostringstream() << ii))->str();
                    string weighthisto = "weight" + weightstring + "_tttt" + numStr;
                    // histo1D[weighthisto]->Draw();
                    histo1D[weighthisto]->Write(("weight" + weightstring + "_tttt" + numStr).c_str());
                    // canv1->SaveAs(("weight"+weightstring+"_tt"+numStr+".png").c_str());
                }
                string MEScalesysname = channel + numStr + sSplitVar + "__" + "NP_overlay_ttttNLO" + "__";

                histo1D[("PU_Up_tttt" + numStr).c_str()]->Write((MEScalesysname + "PUUp").c_str());
                histo1D[("PU_Down_tttt" + numStr).c_str()]->Write((MEScalesysname + "PUDown").c_str());
                histo1D[("btag_lightUp_tttt" + numStr).c_str()]->Write((MEScalesysname + "btag_lightUp").c_str());
                histo1D[("btag_lightDown_tttt" + numStr).c_str()]->Write((MEScalesysname + "btag_lightDown").c_str());
                histo1D[("btag_heavyUp_tttt" + numStr).c_str()]->Write((MEScalesysname + "btag_heavyUp").c_str());
                histo1D[("btag_heavyDown_tttt" + numStr).c_str()]->Write((MEScalesysname + "btag_heavyDown").c_str());
                histo1D[("btagWeightCSVLF_Up_tttt" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVLFUp").c_str());
                histo1D[("btagWeightCSVLF_Down_tttt" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVLFDown").c_str());
                histo1D[("btagWeightCSVHF_Up_tttt" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVHFUp").c_str());
                histo1D[("btagWeightCSVHF_Down_tttt" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVHFDown").c_str());
                histo1D[("btagWeightCSVHFStats1_Up_tttt" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats1Up").c_str());
                histo1D[("btagWeightCSVHFStats1_Down_tttt" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats1Down").c_str());
                histo1D[("btagWeightCSVHFStats2_Up_tttt" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats2Up").c_str());
                histo1D[("btagWeightCSVHFStats2_Down_tttt" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats2Down").c_str());
                histo1D[("btagWeightCSVLFStats1_Up_tttt" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats1Up").c_str());
                histo1D[("btagWeightCSVLFStats1_Down_tttt" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats1Down").c_str());
                histo1D[("btagWeightCSVLFStats2_Up_tttt" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats2Up").c_str());
                histo1D[("btagWeightCSVLFStats2_Down_tttt" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats2Down").c_str());
                histo1D[("btagWeightCSVCFErr1_Up_tttt" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr1Up").c_str());
                histo1D[("btagWeightCSVCFErr1_Down_tttt" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr1Down").c_str());
                histo1D[("btagWeightCSVCFErr2_Up_tttt" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr2Up").c_str());
                histo1D[("btagWeightCSVCFErr2_Down_tttt" + numStr).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr2Down").c_str());                
                MSPlot[plotname.c_str()]->setDataLumi(Luminosity);
            }
        }
    } // end of dataset for loop
    for(int s = fbSplit; s <= ftSplit; s += fwSplit) {
        numStr = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        plotname = sVarofinterest + numStr + sSplitVar;
        histo1D[("TTJets_Rare" + plotname).c_str()]->Write((channel + numStr + sSplitVar + "__TTRare__nominal").c_str());
        //histo1D[("EW" + plotname).c_str()]->Write((channel + numStr + sSplitVar + "__EW__nominal").c_str());
    }
    
    
    GetScaleEnvelopeSplit(nBins, lScale, plotLow, plotHigh, leptoAbbr, shapefile, errorfile, channel, sVarofinterest,
        sSplitVar, fbSplit, ftSplit, fwSplit, xmlNom, CraneenPath, shapefileName, mainTTbarSample);
    GetScaleEnvelopeSplit_tttt(nBins, lScale, plotLow, plotHigh, leptoAbbr, shapefile, errorfile, channel, sVarofinterest,
        sSplitVar, fbSplit, ftSplit, fwSplit, xmlNom, CraneenPath, shapefileName, mainTTbarSample);
    GetMatchingSplit(nBins, lScale, plotLow, plotHigh, leptoAbbr, shapefile, errorfile, channel, sVarofinterest, xmlNom,
        CraneenPath, mainTTbarSample, otherTTbarsample, sSplitVar, fbSplit, ftSplit, fwSplit);
    errorfile->Close();

    // treeLoader.UnLoadDataset();

    string MEScaleFileDir = "ScaleFiles" + leptoAbbr + "_light";
    mkdir(MEScaleFileDir.c_str(), 0777);
    string MEScaleFileName = MEScaleFileDir + "/Error" + sVarofinterest + ".root";
    // MSPlot[plotname.c_str()]->setErrorBandFile(
    // MEScaleFileName.c_str()); // set error file for uncertainty bands on multisample plot
    MSPlot[plotname.c_str()]->setDataLumi(Luminosity);
    for(map<string, MultiSamplePlot*>::const_iterator it = MSPlot.begin(); it != MSPlot.end(); it++) {
        string name = it->first;
        MultiSamplePlot* temp = it->second;
        temp->setDataLumi(35822);

        temp->setErrorBandFile(MEScaleFileName.c_str()); // set error file for uncertainty bands on multisample plot
        temp->Draw(sVarofinterest.c_str(), 0, false, true, true, 20);
        temp->Write(shapefile, name, true, pathPNG, "eps");
        temp->Write(shapefile, name, true, pathPNG, "root");
    }

    for(int s = fbSplit; s <= ftSplit; s += fwSplit) {
        numStr = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        plotname = sVarofinterest + numStr + sSplitVar;
        MSPlot.erase(plotname);
    }
};

void GetPostFits(int nBins, float lScale, float plotLow, float plotHigh, string leptoAbbr, TFile *shapefile,
TFile *errorfile, string channel, string sVarofinterest, string sSplitVar1, float fbSplit1, float ftSplit1, float
fwSplit1, string sSplitVar2, float fbSplit2, float ftSplit2, float fwSplit2, string xmlNom, string CraneenPath, string shapefileName, string units)
{
    TFile * fileOpen = new TFile("/afs/cern.ch/work/l/lowang/CMSSW_7_4_7/src/HiggsAnalysis/CombinedLimit/WorkingArea/card_shapes.root");

    const char *xmlfile = xmlNom.c_str(); cout << "used config file: " << xmlfile << endl;

    string mainTTbarSample;
    string otherTTbarsample;
    cout<<"channel  "<<channel<<endl;
    if(channel == "ttttmu"||channel == "ttttel"){
        mainTTbarSample = "TTJets_powheg";
        otherTTbarsample = "TTJets_MLM";
    }
    else{
        mainTTbarSample = "TTDileptMG";
        otherTTbarsample = "TTDileptPowheg";
    }
    string chanText, chanNum;
    if(channel == "ttttmu"){
        chanText = "Single Lepton: #mu";
        chanNum = "2";}
    else if(channel == "ttttel"){
        chanText = "Single Lepton: e";
        chanNum = "1";}
    else if(channel == "ttttmumu"){
        chanText = "Dilepton: #mu#mu";leptoAbbr="mumu";
    }
    else if(channel == "ttttmuel"){
        chanText = "Dilepton: e#mu";leptoAbbr="muel";
    }
    else if(channel == "ttttmumu"){
        chanText = "Dilepton: ee";leptoAbbr="elel";
    }
    else if(channel == "comb"){
        chanText = "Dilepton: Combined";
    }
    ///////////////////////////////////////////////////////////// Load Datasets
    ////////////////////////////////////////////////////////////////////cout<<"loading...."<<endl;
    TTreeLoader treeLoader;
    vector < Dataset* > datasets;                   //cout<<"vector filled"<<endl;
    treeLoader.LoadDatasets (datasets, xmlfile);    //cout<<"datasets loaded"<<endl;

    // //***************************************************CREATING PLOTS****************************************************
    string plotname;   ///// Jet Split plot
    string plotaxis = plotVarNames(sVarofinterest);
    string dataSetName;
    string numStr1;
    string numStr2;
    string sbSplit1 = static_cast<ostringstream*>( &(ostringstream() << fbSplit1) )->str();
    string stSplit1 = static_cast<ostringstream*>( &(ostringstream() << ftSplit1) )->str();
    string swSplit1 = static_cast<ostringstream*>( &(ostringstream() << fwSplit1) )->str();
    string sbSplit2 = static_cast<ostringstream*>( &(ostringstream() << fbSplit2) )->str();
    string stSplit2 = static_cast<ostringstream*>( &(ostringstream() << ftSplit2) )->str();
    string swSplit2 = static_cast<ostringstream*>( &(ostringstream() << fwSplit2) )->str();
    string pathPNG = "FourTop_Light";
    pathPNG += leptoAbbr;
    pathPNG += "_MSPlots/";
    mkdir(pathPNG.c_str(), 0777); // cout <<"Making directory :"<< pathPNG  <<endl;     //make directory
    for(int s = fbSplit1; s <= ftSplit1; s+=fwSplit1)
    {
        numStr1 = static_cast<ostringstream*>( &(ostringstream() << s) )->str();
        for(int t2 = fbSplit2; t2<= ftSplit2; t2+=fwSplit2){
            numStr2 = static_cast<ostringstream*>( &(ostringstream() << t2) )->str();
            plotname =leptoAbbr + channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 +"_postfit";
            // Stack[plotname.c_str()] = new MultiSamplePlot(datasets, plotname.c_str(), nBins, plotLow, plotHigh, sVarofinterest.c_str());
            string textplot1, textplot2;
            if(s<ftSplit1){
                textplot1 = " Jets  ";
            }
            else textplot1= "+ Jets  ";
            if(t2<ftSplit2){
                textplot2 = " b-tags";
            }
            else textplot2= "+ b-tags";
            
            // MSPlot[plotname.c_str()] = new MultiSamplePlot(datasets, plotname.c_str(), nBins, plotLow, plotHigh,
            //     plotaxis.c_str(), "Events", (chanText+ " " + numStr1 + textplot1 + numStr2 + textplot2).c_str(), units);

            THStack * stackPlot = new THStack(("postfit"+ numStr1 + textplot1 + numStr2 + textplot2).c_str(),("postfit"+ numStr1 + textplot1 + numStr2 + textplot2).c_str());

            for(int d = 0; d < datasets.size(); d++) // Loop through datasets
            {
                dataSetName = datasets[d]->Name();
                cout << "Dataset:  :" << dataSetName << endl;
                const char * postPlotName = ((leptoAbbr+"_"+channel+numStr1 + sSplitVar1 + numStr2 + sSplitVar2+"_postfit/"+dataSetName).c_str());
                // string postPlotName = static_cast<ostringstream*>(&(ostringstream() << postPlotName1))->str();
                cout<<postPlotName<<endl;
                bool bExists = fileOpen->GetListOfKeys()->Contains(postPlotName);
                cout<<"Exists: "<<bExists<<endl;
                if(bExists){
                    TH1F *tempHist = (TH1F*)fileOpen->Get(postPlotName);
                    stackPlot->Add(tempHist);
                    // MSPlot[plotname.c_str()]->AddDataHisto(tempHist);
                }
            }
            shapefile->cd();
            TCanvas * stackCanv = new TCanvas("cs","cs",10,10,700,900);
            stackPlot->Draw();
            stackPlot->Write((plotname).c_str());
            stackCanv->SaveAs(plotname.c_str());
        }
    }

    // for(map<string, MultiSamplePlot*>::const_iterator it = MSPlot.begin(); it != MSPlot.end(); it++) {
    //     string name = it->first;
    //     MultiSamplePlot* temp = it->second;
    //     temp->setDataLumi(2600);

    //     // temp->setErrorBandFile(MEScaleFileName.c_str()); // set error file for uncertainty bands on multisample plot
    //     temp->Draw(sVarofinterest.c_str(), 0, false, false, true, 20);
    //     temp->Write(shapefile, name, true, pathPNG, "eps");
    // }

}

void Split2DatasetPlotter(int nBins,
    float lScale,
    float plotLow,
    float plotHigh,
    string leptoAbbr,
    TFile* shapefile,
    TFile* errorfile,
    string channel,
    string sVarofinterest,
    string sSplitVar1,
    float fbSplit1,
    float ftSplit1,
    float fwSplit1,
    string sSplitVar2,
    float fbSplit2,
    float ftSplit2,
    float fwSplit2,
    string xmlNom,
    string CraneenPath,
    string shapefileName,
    string units)
{
    cout << "" << endl;
    cout << "RUNNING NOMINAL DATASETS" << endl;
    cout << "" << endl;
    shapefile->cd();
    errorfile->mkdir(("MultiSamplePlot_" + sVarofinterest).c_str());

    const char* xmlfile = xmlNom.c_str();
    cout << "used config file: " << xmlfile << endl;
    float Luminosity;
    string pathPNG = "FourTop_Light";
    pathPNG += leptoAbbr;
    pathPNG += "_MSPlots/";
    mkdir(pathPNG.c_str(), 0777);
    cout << "Making directory :" << pathPNG << endl; // make directory
    string mainTTbarSample;
    string otherTTbarsample;
    cout << "channel  " << channel << endl;
    string chanText;
    cout << "channel  " << channel << endl;
    if(channel == "ttttmu" || channel == "ttttel") {
        mainTTbarSample = "TTJets_powheg";
        otherTTbarsample = "TTJets_MLM";
    } else {
        mainTTbarSample = "TTJetsPowheg";
        otherTTbarsample = "TTJetsMG";
    }
    if(channel == "ttttmu")
        chanText = "Single Lepton: #mu";
    else if(channel == "ttttel")
        chanText = "Single Lepton: e";
    else if(channel == "ttttmumu"){
        chanText = "Dilepton: #mu#mu";
        Luminosity = 5743.725979478
                +2573.399420069
                +4248.383597366
                +4009.132398404
                +3101.618412335
                +7540.487735974
                +8390.540446658+215.149415251
                ;
    } else if(channel == "ttttmuel"){
        chanText = "Dilepton: e#mu";
        Luminosity = 5743.725979478
                +2573.399420069
                +4248.383597366
                +4009.132398404
                +3101.618412335
                +7540.487735974
                +8390.540446658+215.149415251
                ;
    } else if(channel == "ttttelel"){
        chanText = "Dilepton: ee";
        Luminosity = 5747.595589414
                +2573.399420069
                +4248.383597366
                +4009.132315299
                +3101.618412335
                +7540.487715338
                +8390.540368893+215.149415251
                ;
    } else if(channel == "comb"){
        chanText = "Dilepton: Combined";
        Luminosity = 5743.725979478
                +2573.399420069
                +4248.383597366
                +4009.132398404
                +3101.618412335
                +7540.487735974
                +8390.540446658+215.149415251
                ;
    }
    ////////////////////////////////////////////////////////////////////
    ////////////////// Load Datasets    cout<<"loading...."<<endl;
    ////////////////////////////////////////////////////////////////////
    
    TTreeLoader treeLoader;
    vector<Dataset*> datasets;                  // cout<<"vector filled"<<endl;
    treeLoader.LoadDatasets(datasets, xmlfile); // cout<<"datasets loaded"<<endl;

    Dataset* ttbar_ll;
    Dataset* ttbar_ll_up;
    Dataset* ttbar_ll_down;
    Dataset* ttbar_cc;
    Dataset* ttbar_cc_up;
    Dataset* ttbar_cc_down;
    Dataset* ttbar_bb;
    Dataset* ttbar_bb_up;
    Dataset* ttbar_bb_down;

    if(split_ttbar) {
        int ndatasets = datasets.size();
        cout << " - splitting TTBar dataset ..." << ndatasets << endl;
        vector<string> ttbar_filenames = datasets[ndatasets - 1]->Filenames();
        cout << "ttbar filenames =  " << ttbar_filenames[0] << endl;

        ttbar_ll = new Dataset("TTJets_ll", "tt + ll", true, 632, 1, 2, 1, 213.4, ttbar_filenames);
        ttbar_cc = new Dataset("TTJets_cc", "tt + cc", true, 633, 1, 2, 1, 6.9, ttbar_filenames);
        ttbar_bb = new Dataset("TTJets_bb", "tt + bb", true, 634, 1, 2, 1, 4.8, ttbar_filenames);

        int newlumi = 551805.763767;
                      //datasets[ndatasets - 1]->EquivalentLumi();
        ttbar_ll->SetEquivalentLuminosity(newlumi);
        ttbar_cc->SetEquivalentLuminosity(newlumi);
        ttbar_bb->SetEquivalentLuminosity(newlumi);

        ttbar_ll->SetColor(kRed);
        ttbar_cc->SetColor(kRed - 3);
        ttbar_bb->SetColor(kRed + 2);

        datasets.push_back(ttbar_bb);
        datasets.push_back(ttbar_cc);
        datasets.push_back(ttbar_ll);
    }

    // //***************************************************CREATING PLOTS****************************************************

    string plotname; ///// Jet Split plot
    string plotaxis = plotVarNames(sVarofinterest);
    string numStr1;
    string numStr2;
    string sbSplit1 = static_cast<ostringstream*>(&(ostringstream() << fbSplit1))->str();
    string stSplit1 = static_cast<ostringstream*>(&(ostringstream() << ftSplit1))->str();
    string swSplit1 = static_cast<ostringstream*>(&(ostringstream() << fwSplit1))->str();
    string sbSplit2 = static_cast<ostringstream*>(&(ostringstream() << fbSplit2))->str();
    string stSplit2 = static_cast<ostringstream*>(&(ostringstream() << ftSplit2))->str();
    string swSplit2 = static_cast<ostringstream*>(&(ostringstream() << fwSplit2))->str();
    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        for(int t2 = fbSplit2; t2 <= ftSplit2; t2 += fwSplit2) {
            numStr2 = static_cast<ostringstream*>(&(ostringstream() << t2))->str();
            plotname = sVarofinterest + numStr1 + sSplitVar1 + numStr2 + sSplitVar2;

            string textplot1, textplot2;
            if(s<ftSplit1){
                textplot1 = " Jets  ";
            }
            else textplot1= "+ Jets  ";
            if(t2<ftSplit2){
                textplot2 = " b-tags";
            }
            else textplot2= "+ b-tags";
            
            MSPlot[plotname.c_str()] = new MultiSamplePlot(datasets, plotname.c_str(), nBins, plotLow, plotHigh, plotaxis.c_str(), units, "Events",
                                                          (chanText+ " " + numStr1 + textplot1 + numStr2 + textplot2).c_str());
            MSPlot[plotname.c_str()]->setPreliminary(prelim_);
            MSPlot[plotname.c_str()]->setMinLogY(0.01);
            histo1D[("TTJets_Rare"+plotname).c_str()] = new TH1F(("TTJets_Rare"+plotname).c_str(), ("TTJets_Rare"+plotname).c_str(), nBins, plotLow, plotHigh);
            histo1D[("TTJets_Rare_plus"+plotname).c_str()] = new TH1F(("TTJets_Rare_plus"+plotname).c_str(), ("TTJets_Rare_plus"+plotname).c_str(), nBins, plotLow, plotHigh);
            histo1D[("EW"+plotname).c_str()] = new TH1F(("EW"+plotname).c_str(), ("EW"+plotname).c_str(), nBins, plotLow, plotHigh);
        }
    }


    plotname = "";

    // //***********************************************OPEN FILES & GET NTUPLES**********************************************
    
    string dataSetName, filepath, histoName;
    int nEntries;
    float ScaleFactor = 1, NormFactor = 1, varofInterest, splitVar,
          GenWeight = 1, weight1 = 1, weight2 = 1, weight3 = 1, weight4 = 1, weight5 = 1, weight6 = 1, weight7 = 1, weight8 = 1,
          ttbar_flav = 1, SFtrigger = 1, SFlepton = 1, SFtrigger_up = 1, SFtrigger_down = 1,
          SFPU = 1, SFPU_up = 1, SFPU_down = 1, SFTopPt = 1, SFTopPt_up = 1, SFTopPt_down = 1, SFbehrends = 1, splitVar1, splitVar2, SFTopPt2,
          SFalphaTune = 1, SFbtagCSV = 1, hdamp_up = 1, hdamp_down = 1, btagWeightCSVLFUp = 1, btagWeightCSVLFDown = 1, btagWeightCSVHFUp = 1,
          btagWeightCSVHFDown = 1, btagWeightCSVHFStats1Up = 1, btagWeightCSVHFStats1Down = 1,
          btagWeightCSVHFStats2Up = 1, btagWeightCSVHFStats2Down = 1, btagWeightCSVLFStats1Up = 1,
          btagWeightCSVLFStats1Down = 1, btagWeightCSVLFStats2Up = 1, btagWeightCSVLFStats2Down = 1,
          btagWeightCSVCFErr1Up = 1, btagWeightCSVCFErr1Down = 1, btagWeightCSVCFErr2Up = 1,
          btagWeightCSVCFErr2Down = 1, weight_ct10 = 1, weight_mmht14 = 1, ttXrew = 1, ttXrew_up = 1, ttXrew_down = 1, lepiso1, lepiso2, BDT_TTRare = -2.0;

    for(int d = 0; d < datasets.size(); d++){

        dataSetName = datasets[d]->Name();
        cout << "Dataset:  :" << dataSetName << endl;
        if(dataSetName.find("TTJets_ll") != string::npos || dataSetName.find("TTJets_cc") != string::npos ||
            dataSetName.find("TTJets_bb") != string::npos) {
            cout << "skip ttbar split datasets!" << endl;
            continue;
        }
        filepath = CraneenPath + dataSetName + "_Run2_TopTree_Study.root";
        // cout<<"filepath: "<<filepath<<endl;

        FileObj[dataSetName.c_str()] = new TFile((filepath).c_str()); // create TFile for each dataset
        string nTuplename = "Craneen__" + leptoAbbr;
        nTuple[dataSetName.c_str()] =
            (TNtuple*)FileObj[dataSetName.c_str()]->Get(nTuplename.c_str()); // get ntuple for each dataset
        nEntries = (int)nTuple[dataSetName.c_str()]->GetEntries();
        cout << "                 nEntries: " << nEntries << endl;

        nTuple[dataSetName.c_str()]->SetBranchAddress(sVarofinterest.c_str(), &varofInterest);
        nTuple[dataSetName.c_str()]->SetBranchAddress("ScaleFactor", &ScaleFactor);
        nTuple[dataSetName.c_str()]->SetBranchAddress("NormFactor", &NormFactor);
        nTuple[dataSetName.c_str()]->SetBranchAddress("GenWeight", &GenWeight);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight1", &weight1);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight2", &weight2);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight3", &weight3);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight4", &weight4);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight5", &weight5);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight6", &weight6);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight7", &weight7);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight8", &weight8);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFtrigger", &SFtrigger);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFtriggerUp", &SFtrigger_up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFtriggerDown", &SFtrigger_down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFlepton", &SFlepton);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight_ct10", &weight_ct10);
        nTuple[dataSetName.c_str()]->SetBranchAddress("weight_mmht14", &weight_mmht14);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFPU", &SFPU);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFPU_up", &SFPU_up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFPU_down", &SFPU_down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("hdampup", &hdamp_up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("hdampdown", &hdamp_down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFtopPt", &SFTopPt);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFtopPtUp", &SFTopPt_up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFtopPtDown", &SFTopPt_down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("ttXrew", &ttXrew);
        nTuple[dataSetName.c_str()]->SetBranchAddress("ttXrew_up", &ttXrew_up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("ttXrew_down", &ttXrew_down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SFbtagCSV", &SFbtagCSV); // SFbtag
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVLFUp", &btagWeightCSVLFUp);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVLFDown", &btagWeightCSVLFDown);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVHFUp", &btagWeightCSVHFUp);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVHFDown", &btagWeightCSVHFDown);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVHFStats1Up", &btagWeightCSVHFStats1Up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVHFStats1Down", &btagWeightCSVHFStats1Down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVHFStats2Up", &btagWeightCSVHFStats2Up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVHFStats2Down", &btagWeightCSVHFStats2Down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVLFStats1Up", &btagWeightCSVLFStats1Up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVLFStats1Down", &btagWeightCSVLFStats1Down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVLFStats2Up", &btagWeightCSVLFStats2Up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVLFStats2Down", &btagWeightCSVLFStats2Down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVCFErr1Up", &btagWeightCSVCFErr1Up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVCFErr1Down", &btagWeightCSVCFErr1Down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVCFErr2Up", &btagWeightCSVCFErr2Up);
        nTuple[dataSetName.c_str()]->SetBranchAddress("btagWeightCSVCFErr2Down", &btagWeightCSVCFErr2Down);
        nTuple[dataSetName.c_str()]->SetBranchAddress("ttbar_flav", &ttbar_flav);
        nTuple[dataSetName.c_str()]->SetBranchAddress(sSplitVar1.c_str(), &splitVar1);
        nTuple[dataSetName.c_str()]->SetBranchAddress(sSplitVar2.c_str(), &splitVar2);
        //nTuple[dataSetName.c_str()]->SetBranchAddress("LeadingLepIso", &lepiso1);
        //nTuple[dataSetName.c_str()]->SetBranchAddress("SubLeadingLepIso", &lepiso2);
/*
if(channel == "ttttmumu") nTuple[dataSetName.c_str()]->SetBranchAddress("BDT_MuMuTTRare_13TeVHadTop", &BDT_TTRare);
else if(channel == "ttttmuel") nTuple[dataSetName.c_str()]->SetBranchAddress("BDT_MuElTTRare_13TeVHadTop", &BDT_TTRare);
else if(channel == "ttttelel") nTuple[dataSetName.c_str()]->SetBranchAddress("BDT_ElElTTRare_13TeVHadTop", &BDT_TTRare);
else BDT_TTRare = -2.0;
*/
        float eqlumi = 1. / datasets[d]->EquivalentLumi();
        cout << "eqlumi: " << eqlumi << endl;

        // for fixed bin width
        for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
            numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();
            for(int t2 = fbSplit2; t2 <= ftSplit2; t2 += fwSplit2) {
                numStr2 = static_cast<ostringstream*>(&(ostringstream() << t2))->str();
                histoName = dataSetName + numStr1 + sSplitVar1 + numStr2 + sSplitVar2;
                histo1D[histoName.c_str()] = new TH1F(histoName.c_str(), histoName.c_str(), nBins, plotLow, plotHigh);
                if(dataSetName.find(mainTTbarSample) != string::npos && dataSetName.find("JES") == string::npos &&
                   dataSetName.find("JER") == string::npos && dataSetName.find("Up") == string::npos && dataSetName.find("Down") == string::npos) {
                    histo1D[("Genweight_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("Genweight_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "Genweight",
                            nBins, plotLow, plotHigh);
                    histo1D[("weight1_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("weight1_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "weight1", nBins,
                            plotLow, plotHigh);
                    histo1D[("weight2_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("weight2_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "weight2", nBins,
                            plotLow, plotHigh);
                    histo1D[("weight3_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("weight3_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "weight3", nBins,
                            plotLow, plotHigh);
                    histo1D[("weight4_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("weight4_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "weight4", nBins,
                            plotLow, plotHigh);
                    histo1D[("weight5_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("weight5_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "weight5", nBins,
                            plotLow, plotHigh);
                    histo1D[("weight6_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("weight6_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "weight6", nBins,
                            plotLow, plotHigh);
                    histo1D[("weight7_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("weight7_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "weight7", nBins,
                            plotLow, plotHigh);
                    histo1D[("weight8_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("weight8_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "weight8", nBins,
                            plotLow, plotHigh);
                    histo1D[("PU_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("PU_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "PU_Up", nBins,
                            plotLow, plotHigh);
                    histo1D[("PU_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("PU_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "PU_Down", nBins,
                            plotLow, plotHigh);
                    histo1D[("TTPT_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("TTPT_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "TTPT_Up", nBins,
                            plotLow, plotHigh);
                    histo1D[("TTPT_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("TTPT_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "TTPT_Down", nBins,
                            plotLow, plotHigh);
                    histo1D[("heavyFlav_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("heavyFlav_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "heavyFlav_Up",
                            nBins, plotLow, plotHigh);
                    histo1D[("heavyFlav_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("heavyFlav_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            "heavyFlav_Down", nBins, plotLow, plotHigh);
		    histo1D[("btagWeightCSVLF_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = 
                        new TH1F(("btagWeightCSVLF_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), 
                            ("btagWeightCSVLF_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
		    histo1D[("btagWeightCSVLF_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
		        new TH1F(("btagWeightCSVLF_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVLF_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
		    histo1D[("btagWeightCSVHF_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = 
                        new TH1F(("btagWeightCSVHF_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVHF_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
		    histo1D[("btagWeightCSVHF_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
		        new TH1F(("btagWeightCSVHF_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVHF_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
		    histo1D[("btagWeightCSVHFStats1_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
		        new TH1F(("btagWeightCSVHFStats1_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVHFStats1_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
		    histo1D[("btagWeightCSVHFStats1_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
		        new TH1F(("btagWeightCSVHFStats1_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVHFStats1_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
		    histo1D[("btagWeightCSVHFStats2_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
		        new TH1F(("btagWeightCSVHFStats2_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVHFStats2_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
		    histo1D[("btagWeightCSVHFStats2_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
		        new TH1F(("btagWeightCSVHFStats2_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVHFStats2_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
		    histo1D[("btagWeightCSVLFStats1_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
		        new TH1F(("btagWeightCSVLFStats1_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVLFStats1_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
		    histo1D[("btagWeightCSVLFStats1_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
		        new TH1F(("btagWeightCSVLFStats1_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVLFStats1_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
		    histo1D[("btagWeightCSVLFStats2_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
		        new TH1F(("btagWeightCSVLFStats2_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVLFStats2_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
		    histo1D[("btagWeightCSVLFStats2_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
		        new TH1F(("btagWeightCSVLFStats2_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVLFStats2_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
		    histo1D[("btagWeightCSVCFErr1_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
		        new TH1F(("btagWeightCSVCFErr1_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVCFErr1_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
		    histo1D[("btagWeightCSVCFErr1_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
		        new TH1F(("btagWeightCSVCFErr1_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVCFErr1_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
		    histo1D[("btagWeightCSVCFErr2_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
		        new TH1F(("btagWeightCSVCFErr2_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVCFErr2_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
		    histo1D[("btagWeightCSVCFErr2_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
		        new TH1F(("btagWeightCSVCFErr2_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVCFErr2_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);  
                    histo1D[("hdamp_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("hdamp_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "hdamp_Up", nBins,
                            plotLow, plotHigh);
                    histo1D[("hdamp_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("hdamp_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "hdamp_Down", nBins,
                            plotLow, plotHigh);
                    histo1D[("TTJetsPDF_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = 
                        new TH1F(("TTJetsPDF_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "TTJetsPDF_Up", nBins,
                            plotLow, plotHigh);
                    histo1D[("TTJetsPDF_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("TTJetsPDF_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "TTJetsPDF_Down", nBins,
                            plotLow, plotHigh);
                    histo1D[("SFjetnormcor_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("SFjetnormcor_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "SFjetnormcor_Up", nBins,
                            plotLow, plotHigh);
                    histo1D[("SFjetnormcor_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("SFjetnormcor_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "SFjetnormcor_Down", nBins,
                            plotLow, plotHigh);

                } else if(dataSetName.find("NP_overlay_ttttNLO") != string::npos && dataSetName.find("JES") == string::npos &&
                          dataSetName.find("JER") == string::npos && dataSetName.find("FSR") == string::npos && dataSetName.find("ISR") == string::npos) {

                    histo1D[("Genweight_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("Genweight_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "Genweight_tttt",
                            nBins, plotLow, plotHigh);
                    histo1D[("weight1_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("weight1_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "weight1_tttt", nBins,
                            plotLow, plotHigh);
                    histo1D[("weight2_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("weight2_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "weight2_tttt", nBins,
                            plotLow, plotHigh);
                    histo1D[("weight3_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("weight3_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "weight3_tttt", nBins,
                            plotLow, plotHigh);
                    histo1D[("weight4_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("weight4_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "weight4_tttt", nBins,
                            plotLow, plotHigh);
                    histo1D[("weight5_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("weight5_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "weight5_tttt", nBins,
                            plotLow, plotHigh);
                    histo1D[("weight6_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("weight6_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "weight6_tttt", nBins,
                            plotLow, plotHigh);
                    histo1D[("weight7_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("weight7_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "weight7_tttt", nBins,
                            plotLow, plotHigh);
                    histo1D[("weight8_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("weight8_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "weight8_tttt", nBins,
                            plotLow, plotHigh);
                    histo1D[("PU_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("PU_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "PU_Up_tttt", nBins,
                            plotLow, plotHigh);
                    histo1D[("PU_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("PU_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "PU_Down_tttt", nBins,
                            plotLow, plotHigh);
                    histo1D[("SFleptrig_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("SFleptrig_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "SFleptrig_Up_tttt", nBins,
                            plotLow, plotHigh);
                    histo1D[("SFleptrig_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("SFleptrig_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "SFleptrig_Down_tttt", nBins,
                            plotLow, plotHigh);
                    histo1D[("btagWeightCSVLF_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("btagWeightCSVLF_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVLF_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("btagWeightCSVLF_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("btagWeightCSVLF_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVLF_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("btagWeightCSVHF_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("btagWeightCSVHF_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVHF_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("btagWeightCSVHF_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("btagWeightCSVHF_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVHF_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("btagWeightCSVHFStats1_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("btagWeightCSVHFStats1_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVHFStats1_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("btagWeightCSVHFStats1_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("btagWeightCSVHFStats1_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVHFStats1_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("btagWeightCSVHFStats2_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("btagWeightCSVHFStats2_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVHFStats2_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("btagWeightCSVHFStats2_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("btagWeightCSVHFStats2_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVHFStats2_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("btagWeightCSVLFStats1_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("btagWeightCSVLFStats1_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVLFStats1_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("btagWeightCSVLFStats1_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("btagWeightCSVLFStats1_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVLFStats1_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("btagWeightCSVLFStats2_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("btagWeightCSVLFStats2_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVLFStats2_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("btagWeightCSVLFStats2_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("btagWeightCSVLFStats2_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVLFStats2_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("btagWeightCSVCFErr1_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("btagWeightCSVCFErr1_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVCFErr1_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("btagWeightCSVCFErr1_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("btagWeightCSVCFErr1_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVCFErr1_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("btagWeightCSVCFErr2_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("btagWeightCSVCFErr2_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVCFErr2_Up_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("btagWeightCSVCFErr2_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("btagWeightCSVCFErr2_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("btagWeightCSVCFErr2_Down_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);  

                }
            }
        }
        /////*****loop through entries and fill plots*****

        //Luminosity = 24325.9;

        float ProjectedLumi = 10000; // pb-1
        float LumiFactor = 1;


        // float LumiFactor = ProjectedLumi/Luminosity;
        for(int j = 0; j < nEntries; j++) {
            nTuple[dataSetName.c_str()]->GetEntry(j);

            // artificial Lumi
            // if(lScale > 0 )
            // {
            //     Luminosity = 1000*lScale;
            // }
            //if(sVarofinterest.find("BDT") != string::npos && varofInterest > 0.3) continue;

            //if(lepiso1>0.15||lepiso2>0.15) continue;
            NormFactor = 1.0;
            SFalphaTune = 1.0; SFbehrends = 1.0;
            //SFTopPt_up = SFTopPt > 1.0? SFTopPt: 1.0;            SFTopPt_down = SFTopPt > 1.0? 1.0: SFTopPt;            SFTopPt = 1.0; 
            if(dataSetName.find("tttt") != string::npos) {
                NormFactor = 1.0 / 0.4214;
            } else if(dataSetName.find("WZZ") != string::npos) {
                NormFactor = 1.1334;
            } else if(dataSetName.find("ZZZ") != string::npos) {
                NormFactor = 1.1667;
            //} else if(dataSetName.find("Rare2TTW") != string::npos && dataSetName.find("Rare2TTWZ") == string::npos) {
            //    NormFactor = 1.0 / 0.5151;
            }
 

            float ttbbReweight = 1, ttbbReweight_up = 1, ttbbReweight_down = 1;
            if(reweight_ttbar && dataSetName.find("TTJets") != string::npos){
                //ttbbReweight = ttXrew;
                if(ttXrew>1.1){
                    ttbbReweight_up = 1.35;//ttXrew_up;
                    ttbbReweight_down = 0.65;//ttXrew_down;
                }
            }

            float cFactor = 1, cFactor_up = 1, cFactor_down = 1;

            if(splitVar1 == 6){ cFactor = 0.9; cFactor_up = 0.93; cFactor_down = 0.87;}
            if(splitVar1 == 7){ cFactor = 0.85; cFactor_up = 0.89; cFactor_down = 0.81;}
            if(splitVar1 >=8){ cFactor = 0.85; cFactor_up = 0.935; cFactor_down = 0.765;}

            bool outsiderange = true;
            string nameEnding = "";
            if(splitVar1 >= ftSplit1){  // Check if this entry belongs in the last bin in var1.  Done here to optimize number of checks
                if(splitVar2 >= ftSplit2) { // Check if this entry belongs in the last bin in var2.
                    plotname = sVarofinterest + stSplit1 + sSplitVar1 + stSplit2 + sSplitVar2;
                    histoName = dataSetName + stSplit1 + sSplitVar1 + stSplit2 + sSplitVar2;
                    nameEnding = stSplit1 + sSplitVar1 + stSplit2 + sSplitVar2;
                    outsiderange = false;
                    //                                cout<<"splitvar2: "<<splitVar2<<endl;
                } else {   // If it doesn't belong in the last bin in var2, find out which it belongs in
                    for(int t2 = fbSplit2; t2 < ftSplit2; t2 += fwSplit2) {
                        if(splitVar2 >= t2 && splitVar2 < (t2 + fwSplit2)){  // splitVar falls inside one of the bins
                            numStr2 = static_cast<ostringstream*>(&(ostringstream() << t2))->str();
                            plotname = sVarofinterest + stSplit1 + sSplitVar1 + numStr2 + sSplitVar2;
                            histoName = dataSetName + stSplit1 + sSplitVar1 + numStr2 + sSplitVar2;
                            nameEnding = stSplit1 + sSplitVar1 + numStr2 + sSplitVar2;

                            outsiderange = false;
                            break;
                        }
                    }
                }
            } else {  // If it doesn't belong in the last bin in var1, find out which it belongs in
                for(int s = fbSplit1; s < ftSplit1; s += fwSplit1) {
                    if(splitVar1 >= s && splitVar1 < (s + fwSplit1)){   // splitVar falls inside one of the bins
                        numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();
                        if(splitVar2 >= ftSplit2) { // Check if this entry belongs in the last bin in var2.
                            plotname = sVarofinterest + numStr1 + sSplitVar1 + stSplit2 + sSplitVar2;
                            histoName = dataSetName + numStr1 + sSplitVar1 + stSplit2 + sSplitVar2;
                            nameEnding = numStr1 + sSplitVar1 + stSplit2 + sSplitVar2;

                            outsiderange = false;
                        } else {  // If it doesn't belong in the last bin, find out which it belongs in
                            for(int t2 = fbSplit2; t2 < ftSplit2; t2 += fwSplit2) {
                                if(splitVar2 >= t2 && splitVar2 < (t2 + fwSplit2)) {  // splitVar falls inside one of the bins
                                    numStr2 = static_cast<ostringstream*>(&(ostringstream() << t2))->str();
                                    plotname = sVarofinterest + numStr1 + sSplitVar1 + numStr2 + sSplitVar2;
                                    histoName = dataSetName + numStr1 + sSplitVar1 + numStr2 + sSplitVar2;
                                    nameEnding = numStr1 + sSplitVar1 + numStr2 + sSplitVar2;

                                    outsiderange = false;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
            if(outsiderange == true) {
                continue;
            }
            if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
                dataSetName.find("DATA") != string::npos || dataSetName.find("NP_overlay_Data") != string::npos) {
                MSPlot[plotname]->Fill(varofInterest, datasets[d], true, 1);
                histo1D[histoName.c_str()]->Fill(varofInterest, 1);
            } else if(dataSetName.find(mainTTbarSample) != string::npos && dataSetName.find("JES") == string::npos &&
                dataSetName.find("JER") == string::npos && dataSetName.find("ISR") == string::npos && dataSetName.find("FSR") == string::npos &&
                dataSetName.find("Up") == string::npos && dataSetName.find("Down") == string::npos) {

                histo1D[("Genweight_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * cFactor * GenWeight);
                histo1D[("weight1_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight1);
                histo1D[("weight2_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight2);
                histo1D[("weight3_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight3);
                histo1D[("weight4_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight4);
                histo1D[("weight5_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight5);
                histo1D[("weight6_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight6);
                histo1D[("weight7_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight7);
                histo1D[("weight8_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight8);
                histo1D[("PU_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU_up * SFTopPt * SFbehrends * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("PU_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU_down * SFTopPt * SFbehrends * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("TTPT_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt_up * SFbehrends * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("TTPT_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt_down * SFbehrends * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("btagWeightCSVLF_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFUp * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("btagWeightCSVLF_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFDown * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("btagWeightCSVHF_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFUp * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("btagWeightCSVHF_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFDown * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("btagWeightCSVHFStats1_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats1Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVHFStats1_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats1Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVHFStats2_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats2Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVHFStats2_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats2Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVLFStats1_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats1Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVLFStats1_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats1Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVLFStats2_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats2Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVLFStats2_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats2Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVCFErr1_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr1Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * 
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVCFErr1_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr1Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVCFErr2_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr2Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVCFErr2_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr2Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("heavyFlav_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight_up * cFactor * GenWeight);
                histo1D[("heavyFlav_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight_down * cFactor * GenWeight);
                histo1D[("hdamp_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * cFactor * hdamp_up * GenWeight);
                histo1D[("hdamp_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * cFactor * hdamp_down * GenWeight);
                histo1D[("TTJetsPDF_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * cFactor * findmax(weight_ct10, weight_mmht14, (float) 1.0) * GenWeight);
                histo1D[("TTJetsPDF_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * cFactor * findmin(weight_ct10, weight_mmht14, (float) 1.0) * GenWeight);
                histo1D[("SFjetnormcor_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        eqlumi * ttbbReweight * cFactor_up * GenWeight);
                histo1D[("SFjetnormcor_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        eqlumi * ttbbReweight * cFactor_down * GenWeight);

                histo1D[histoName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                        SFPU * SFTopPt * SFbehrends * GenWeight * Luminosity * eqlumi * ttbbReweight * cFactor);

                if(split_ttbar) {
                    if(ttXrew < 1) { 
                        MSPlot[plotname]->Fill(varofInterest, ttbar_ll, true, NormFactor * GenWeight * SFtrigger * SFlepton *
                         SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * cFactor);
                    } else if(ttXrew > 1) { 
                        MSPlot[plotname]->Fill(varofInterest, ttbar_bb, true, NormFactor * GenWeight * SFtrigger * SFlepton *
                         SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * cFactor);
                    } else {
                        MSPlot[plotname]->Fill(varofInterest, ttbar_cc, true, NormFactor * GenWeight * SFtrigger * SFlepton *
                         SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * cFactor);
                    }
                } else {
                    MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * GenWeight * SFtrigger * SFlepton *
                         SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * ttbbReweight * cFactor);
                }

                //histo1D[("ttbarTTX"+plotname).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV *
                //        SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                //        ttbbReweight* LumiFactor);

            } else if(dataSetName.find("NP_overlay_ttttNLO") != string::npos && dataSetName.find("JES") == string::npos &&
                dataSetName.find("JER") == string::npos && dataSetName.find("ISR") == string::npos && dataSetName.find("FSR") == string::npos &&
                dataSetName.find("Up") == string::npos && dataSetName.find("Down") == string::npos) {

                histo1D[("Genweight_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor * GenWeight);
                histo1D[("weight1_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor * weight1);
                histo1D[("weight2_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor * weight2);
                histo1D[("weight3_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor * weight3);
                histo1D[("weight4_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor * weight4);
                histo1D[("weight5_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor * weight5);
                histo1D[("weight6_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor * weight6);
                histo1D[("weight7_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor * weight7);
                histo1D[("weight8_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor * weight8);
                histo1D[("PU_Up_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU_up * SFTopPt * SFbehrends * Luminosity *
                        eqlumi * ttbbReweight * LumiFactor * GenWeight);
                histo1D[("PU_Down_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU_down * SFTopPt * SFbehrends * Luminosity *
                        eqlumi * ttbbReweight * LumiFactor * GenWeight);
                histo1D[("btagWeightCSVLF_Up_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFUp * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVLF_Down_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFDown * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVHF_Up_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFUp * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVHF_Down_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFDown * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVHFStats1_Up_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats1Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVHFStats1_Down_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats1Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVHFStats2_Up_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats2Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVHFStats2_Down_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats2Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVLFStats1_Up_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats1Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVLFStats1_Down_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats1Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVLFStats2_Up_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats2Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVLFStats2_Down_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats2Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVCFErr1_Up_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr1Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVCFErr1_Down_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr1Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVCFErr2_Up_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr2Up * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVCFErr2_Down_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr2Down * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);

                histo1D[histoName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt *
                        SFbehrends * GenWeight * Luminosity * eqlumi * ttbbReweight);
                MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        ttbbReweight * LumiFactor * GenWeight);
            } else if(dataSetName.find("Rare1") != string::npos) {
                histo1D[("TTJets_Rare"+plotname).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV *
                        SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                        ttbbReweight* LumiFactor);

                histo1D[histoName.c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV *
                        SFalphaTune * SFPU * SFTopPt * SFbehrends * GenWeight * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor);

                MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        ttbbReweight * LumiFactor * GenWeight);
            } else if( dataSetName.find("Rare2") != string::npos) {
                histo1D[("TTJets_Rare_plus"+plotname).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                        SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                        ttbbReweight* LumiFactor);

                histo1D[histoName.c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV *
                        SFalphaTune * SFPU * SFTopPt * SFbehrends * GenWeight * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor);

                MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        ttbbReweight * LumiFactor * GenWeight);
            } else if( dataSetName.find("EW") != string::npos || dataSetName.find("DYJets") != string::npos) {
                histo1D[("EW"+plotname).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                        SFPU * SFTopPt * SFbehrends * Luminosity * GenWeight * eqlumi *
                        ttbbReweight* LumiFactor);

                histo1D[histoName.c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV *
                        SFalphaTune * SFPU * SFTopPt * SFbehrends * GenWeight * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor);

                MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        ttbbReweight * LumiFactor * GenWeight);
            } else if(dataSetName.find(otherTTbarsample) == string::npos && dataSetName.find("TTUE") == string::npos &&
                      dataSetName.find("JES") == string::npos && dataSetName.find("JER") == string::npos &&
                      dataSetName.find("ISR") == string::npos && dataSetName.find("FSR") == string::npos &&
                      dataSetName.find("Up") == string::npos && dataSetName.find("Down") == string::npos) {
                MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * SFbehrends * Luminosity *
                        ttbbReweight * LumiFactor * GenWeight);
                histo1D[histoName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt *
                        SFbehrends * GenWeight * Luminosity * eqlumi * ttbbReweight * LumiFactor);
            } else if(dataSetName.find("TTJets") != string::npos){
                histo1D[histoName.c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV *
                        SFalphaTune * SFPU * SFTopPt * SFbehrends * GenWeight * Luminosity * eqlumi *
                        ttbbReweight * cFactor);
            } else {
                histo1D[histoName.c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV *
                        SFalphaTune * SFPU * SFTopPt * SFbehrends * GenWeight * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor);
            }
        }

        shapefile->cd();
        TCanvas* canv = new TCanvas();
        for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
            numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();
            for(int t2 = fbSplit2; t2 <= ftSplit2; t2 += fwSplit2) {
                numStr2 = static_cast<ostringstream*>(&(ostringstream() << t2))->str();
                plotname = sVarofinterest + numStr1 + sSplitVar1 + numStr2 + sSplitVar2;
                histoName = dataSetName + numStr1 + sSplitVar1 + numStr2 + sSplitVar2;
                histo1D[histoName.c_str()]->Draw();
                string writename = "";
                if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos || dataSetName.find("DATA") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__data_obs__nominal";
                } else if(dataSetName.find("JESUp") != string::npos&& dataSetName.find(mainTTbarSample) != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__JESUp";
                } else if(dataSetName.find("JESDown") != string::npos&& dataSetName.find(mainTTbarSample) != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__JESDown";

                } else if(dataSetName.find("TTJets_SubTotalPileUpUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__SubTotalPileUpUp";
                } else if(dataSetName.find("TTJets_SubTotalPileUpDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__SubTotalPileUpDown";
                } else if(dataSetName.find("TTJets_SubTotalRelativeUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__SubTotalRelativeUp";
                } else if(dataSetName.find("TTJets_SubTotalRelativeDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__SubTotalRelativeDown";
                } else if(dataSetName.find("TTJets_SubTotalPtUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__SubTotalPtUp";
                } else if(dataSetName.find("TTJets_SubTotalPtDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__SubTotalPtDown";
                } else if(dataSetName.find("TTJets_SubTotalScaleUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__SubTotalScaleUp";
                } else if(dataSetName.find("TTJets_SubTotalScaleDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__SubTotalScaleDown";
                } else if(dataSetName.find("TTJets_SubTotalFlavorUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__SubTotalFlavorUp";
                } else if(dataSetName.find("TTJets_SubTotalFlavorDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__SubTotalFlavorDown";

                } else if(dataSetName.find("JERUp") != string::npos&& dataSetName.find(mainTTbarSample) != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__JERUp";
                } else if(dataSetName.find("JERDown") != string::npos&& dataSetName.find(mainTTbarSample) != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__JERDown";
                } else if(dataSetName.find("TTUEUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__TTUEUp";
                } else if(dataSetName.find("TTUEDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX"  + "__TTUEDown";
                } else if(dataSetName.find("TTISRUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__TTISRUp";
                } else if(dataSetName.find("TTISRDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__TTISRDown";
                } else if(dataSetName.find("TTFSRUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__TTFSRUp";
                } else if(dataSetName.find("TTFSRDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__TTFSRDown";
                } else if(dataSetName.find("ttttISRUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__TTTTISRUp";
                } else if(dataSetName.find("ttttISRDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__TTTTISRDown";
                } else if(dataSetName.find("ttttFSRUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__TTTTFSRUp";
                } else if(dataSetName.find("ttttFSRDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__TTTTFSRDown";
                } else if(dataSetName.find("JESUp") != string::npos && dataSetName.find("tttt") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__JESUp";
                } else if(dataSetName.find("JESDown") != string::npos && dataSetName.find("tttt") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__JESDown";

                } else if(dataSetName.find("ttttNLO_SubTotalPileUpUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__SubTotalPileUpUp";
                } else if(dataSetName.find("ttttNLO_SubTotalPileUpDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__SubTotalPileUpDown";
                } else if(dataSetName.find("ttttNLO_SubTotalRelativeUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__SubTotalRelativeUp";
                } else if(dataSetName.find("ttttNLO_SubTotalRelativeDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__SubTotalRelativeDown";
                } else if(dataSetName.find("ttttNLO_SubTotalPtUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__SubTotalPtUp";
                } else if(dataSetName.find("ttttNLO_SubTotalPtDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__SubTotalPtDown";
                } else if(dataSetName.find("ttttNLO_SubTotalScaleUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__SubTotalScaleUp";
                } else if(dataSetName.find("ttttNLO_SubTotalScaleDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__SubTotalScaleDown";
                } else if(dataSetName.find("ttttNLO_SubTotalFlavorUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__SubTotalFlavorUp";
                } else if(dataSetName.find("ttttNLO_SubTotalFlavorDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__SubTotalFlavorDown";

                } else if(dataSetName.find("JERUp") != string::npos && dataSetName.find("tttt") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__JERUp";
                } else if(dataSetName.find("JERDown") != string::npos && dataSetName.find("tttt") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__JERDown";
                } else if(dataSetName.find("TTJetsPowheg") != string::npos && dataSetName.find("Up") == string::npos &&
                          dataSetName.find("Down") == string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__ttbarTTX" + "__nominal";
                } else {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + dataSetName + "__nominal";
                }
                // cout<<"writename  :"<<writename<<endl;
                histo1D[histoName.c_str()]->Write((writename).c_str());




                //canv->SaveAs((pathPNG + histoName + ".png").c_str());
                if(dataSetName.find(mainTTbarSample) != string::npos && dataSetName.find("JES") == string::npos &&
                    dataSetName.find("JER") == string::npos && dataSetName.find("FSR") == string::npos && dataSetName.find("ISR") == string::npos) {
                    cout << "  making weights histos" << endl;

                    // TCanvas *canv0 = new TCanvas();
                    // histo1D[("Genweight_tt"+numStr).c_str()]->Draw();
                    histo1D[("Genweight_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write(
                        ("Genweight_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
                    // canv0->SaveAs(("Genweight_tt"+numStr+".png").c_str());

                    for(int ii = 1; ii < 9; ii++) {
                        // TCanvas *canv1 = new TCanvas();
                        string weightstring = static_cast<ostringstream*>(&(ostringstream() << ii))->str();
                        string weighthisto = "weight" + weightstring + "_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2;
                        // histo1D[weighthisto]->Draw();
                        histo1D[weighthisto]->Write(("weight" + weightstring + "_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
                        // canv1->SaveAs(("weight"+weightstring+"_tt"+numStr+".png").c_str());
                    }
                    string MEScalesysname = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__ttbarTTX" + "__";

                    histo1D[("PU_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "PUUp").c_str());
                    histo1D[("PU_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "PUDown").c_str());
                    histo1D[("SFjetnormcor_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "SFjetnormUp").c_str());
                    histo1D[("SFjetnormcor_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "SFjetnormDown").c_str());
                    histo1D[("TTPT_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "TTPTUp").c_str());
                    histo1D[("TTPT_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "TTPTDown").c_str());
                    histo1D[("hdamp_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "TTJets_HDAMPUp").c_str());
                    histo1D[("hdamp_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "TTJets_HDAMPDown").c_str());
                    histo1D[("TTJetsPDF_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "TTJets_PDFUp").c_str());
                    histo1D[("TTJetsPDF_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "TTJets_PDFDown").c_str());
                    histo1D[("heavyFlav_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "heavyFlavUp").c_str());
                    histo1D[("heavyFlav_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "heavyFlavDown").c_str());
	            histo1D[("btagWeightCSVLF_Up"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVLFUp").c_str());
	            histo1D[("btagWeightCSVLF_Down"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVLFDown").c_str());
	            histo1D[("btagWeightCSVHF_Up"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVHFUp").c_str());
	            histo1D[("btagWeightCSVHF_Down"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVHFDown").c_str());
	            histo1D[("btagWeightCSVHFStats1_Up"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats1Up").c_str());
	            histo1D[("btagWeightCSVHFStats1_Down"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats1Down").c_str());
	            histo1D[("btagWeightCSVHFStats2_Up"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats2Up").c_str());
	            histo1D[("btagWeightCSVHFStats2_Down"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats2Down").c_str());
	            histo1D[("btagWeightCSVLFStats1_Up"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats1Up").c_str());
	            histo1D[("btagWeightCSVLFStats1_Down"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats1Down").c_str());
	            histo1D[("btagWeightCSVLFStats2_Up"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats2Up").c_str());
	            histo1D[("btagWeightCSVLFStats2_Down"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats2Down").c_str());
	            histo1D[("btagWeightCSVCFErr1_Up"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr1Up").c_str());
	            histo1D[("btagWeightCSVCFErr1_Down"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr1Down").c_str());
	            histo1D[("btagWeightCSVCFErr2_Up"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr2Up").c_str());
	            histo1D[("btagWeightCSVCFErr2_Down"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr2Down").c_str());                    
                }
                if(dataSetName.find("NP_overlay_tttt") != string::npos && dataSetName.find("JES") == string::npos &&
                    dataSetName.find("JER") == string::npos && dataSetName.find("FSR") == string::npos && dataSetName.find("ISR") == string::npos) {
                    cout << "  making weights histos" << endl;

                    // TCanvas *canv0 = new TCanvas();
                    // histo1D[("Genweight_tt"+numStr).c_str()]->Draw();
                    histo1D[("Genweight_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write(
                        ("Genweight_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
                    // canv0->SaveAs(("Genweight_tt"+numStr+".png").c_str());

                    for(int ii = 1; ii < 9; ii++) {
                        // TCanvas *canv1 = new TCanvas();
                        string weightstring = static_cast<ostringstream*>(&(ostringstream() << ii))->str();
                        string weighthisto = "weight" + weightstring + "_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2;
                        // histo1D[weighthisto]->Draw();
                        histo1D[weighthisto]->Write(("weight" + weightstring + "_tttt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
                        // canv1->SaveAs(("weight"+weightstring+"_tt"+numStr+".png").c_str());
                    }
                    string MEScalesysname = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__";

                    histo1D[("PU_Up_tttt"+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "PUUp").c_str());
                    histo1D[("PU_Down_tttt"+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "PUDown").c_str());
	            histo1D[("btagWeightCSVLF_Up_tttt"+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVLFUp").c_str());
	            histo1D[("btagWeightCSVLF_Down_tttt"+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVLFDown").c_str());
	            histo1D[("btagWeightCSVHF_Up_tttt"+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVHFUp").c_str());
	            histo1D[("btagWeightCSVHF_Down_tttt"+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVHFDown").c_str());
	            histo1D[("btagWeightCSVHFStats1_Up_tttt"+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats1Up").c_str());
	            histo1D[("btagWeightCSVHFStats1_Down_tttt"+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats1Down").c_str());
	            histo1D[("btagWeightCSVHFStats2_Up_tttt"+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats2Up").c_str());
	            histo1D[("btagWeightCSVHFStats2_Down_tttt"+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats2Down").c_str());
	            histo1D[("btagWeightCSVLFStats1_Up_tttt"+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats1Up").c_str());
	            histo1D[("btagWeightCSVLFStats1_Down_tttt"+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats1Down").c_str());
	            histo1D[("btagWeightCSVLFStats2_Up_tttt"+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats2Up").c_str());
	            histo1D[("btagWeightCSVLFStats2_Down_tttt"+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats2Down").c_str());
	            histo1D[("btagWeightCSVCFErr1_Up_tttt"+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr1Up").c_str());
	            histo1D[("btagWeightCSVCFErr1_Down_tttt"+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr1Down").c_str());
	            histo1D[("btagWeightCSVCFErr2_Up_tttt"+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr2Up").c_str());
	            histo1D[("btagWeightCSVCFErr2_Down_tttt"+ numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr2Down").c_str());                
                }                
            }
        }
        FileObj[dataSetName.c_str()]->Close();
    } // end dataset loop
    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        for(int t2 = fbSplit2; t2 <= ftSplit2; t2 += fwSplit2) {
            numStr2 = static_cast<ostringstream*>(&(ostringstream() << t2))->str();
            plotname = sVarofinterest + numStr1 + sSplitVar1 + numStr2 + sSplitVar2;
            histo1D[("TTJets_Rare"+plotname).c_str()]->Write((channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__TTRARE__nominal").c_str());
            histo1D[("TTJets_Rare_plus"+plotname).c_str()]->Write((channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__TTRARE_plus__nominal").c_str());
            histo1D[("EW"+plotname).c_str()]->Write((channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__EW__nominal").c_str());
        }
    }
    GetScaleEnvelopeSplit2_tttt(nBins, lScale, plotLow, plotHigh, leptoAbbr, shapefile, errorfile, channel, sVarofinterest,
        sSplitVar1, fbSplit1, ftSplit1, fwSplit1, sSplitVar2, fbSplit2, ftSplit2, fwSplit2, xmlNom, CraneenPath,
        shapefileName, mainTTbarSample);
    GetScaleEnvelopeSplit2(nBins, lScale, plotLow, plotHigh, leptoAbbr, shapefile, errorfile, channel, sVarofinterest,
        sSplitVar1, fbSplit1, ftSplit1, fwSplit1, sSplitVar2, fbSplit2, ftSplit2, fwSplit2, xmlNom, CraneenPath,
        shapefileName, mainTTbarSample);
    //GetMatchingSplit2(nBins, lScale, plotLow, plotHigh, leptoAbbr, shapefile, errorfile, channel, sVarofinterest,
    //    xmlNom, CraneenPath, mainTTbarSample, otherTTbarsample, sSplitVar1, fbSplit1, ftSplit1, fwSplit1, sSplitVar2,
    //    fbSplit2, ftSplit2, fwSplit2);
    GetErrorBandSplit2(nBins, lScale, plotLow, plotHigh, leptoAbbr, shapefile, errorfile, channel, sVarofinterest,
        sSplitVar1, fbSplit1, ftSplit1, fwSplit1, sSplitVar2, fbSplit2, ftSplit2, fwSplit2, xmlNom, CraneenPath,
        shapefileName, mainTTbarSample);
    errorfile->Close();
    // treeLoader.UnLoadDataset();

    string MEScaleFileDir = "ScaleFiles" + leptoAbbr + "_light";
    mkdir(MEScaleFileDir.c_str(), 0777);
    string MEScaleFileName = MEScaleFileDir + "/Error" + sVarofinterest + ".root";
    // MSPlot[plotname.c_str()]->setErrorBandFile(MEScaleFileName.c_str()); //set error file for uncertainty bands on
    // multisample plot
    // MSPlot[plotname.c_str()]->setDataLumi(2600);

    for(map<string, MultiSamplePlot*>::const_iterator it = MSPlot.begin(); it != MSPlot.end(); it++) {
        string name = it->first;
        MultiSamplePlot* temp = it->second;
        temp->setDataLumi(35822);

        temp->setErrorBandFile(MEScaleFileName.c_str()); // set error file for uncertainty bands on multisample plot
        temp->Draw(sVarofinterest.c_str(), 2, false, true, true, 20);//bool addRatioErrorBand, bool addErrorBand, bool ErrorBandAroundTotalInput
        temp->Write(shapefile, name, true, pathPNG, "eps");
        temp->Write(shapefile, name, true, pathPNG, "root");
    }
    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        for(int t2 = fbSplit2; t2 <= ftSplit2; t2 += fwSplit2) {
            numStr2 = static_cast<ostringstream*>(&(ostringstream() << t2))->str();
            plotname = sVarofinterest + numStr1 + sSplitVar1 + numStr2 + sSplitVar2;
            MSPlot.erase(plotname);
        }
    }
};

void DataCardProducer(string VoI,
    TFile* shapefile,
    string shapefileName,
    string channel,
    string leptoAbbr,
    string xmlNom,
    float lScale)
{
    TTreeLoader treeLoader;
    vector<Dataset*> datasets; // cout<<"vector filled"<<endl;
    const char* xmlfile = xmlNom.c_str();
    treeLoader.LoadDatasets(datasets, xmlfile); // cout<<"datasets loaded"<<endl;
    int nDatasets = datasets.size();
    TH1F* tempHisto;
    float tempEntries;
    int nChannels = 1;
    int howmanyMC = 0;
    vector<string> MCdatasets; // contains only MC samples required in datacard
    cout << "\nPRODUCING DATACARD\n" << endl;

    string mainTTbarsample;
    string otherTTbarsample;
    cout << "channel  " << channel << endl;
    if(channel == "ttttmu" || channel == "ttttel") {
        mainTTbarsample = "TTJets_powheg";
        otherTTbarsample = "TTJets_MLM";
    } else {
        mainTTbarsample = "TTJetsPowheg";
        otherTTbarsample = "TTJetsMG";
    }

    string binname, histoName, dataSetName, datacardname;
    ofstream card;
    string slScale = intToStr(lScale);

    if(lScale > 0) {
        datacardname = "datacard" + leptoAbbr + "_" + VoI + "_" + slScale + "_inc.txt";
    } else {
        datacardname = "datacard" + leptoAbbr + "_" + VoI + "_inc.txt";
    }
    card.open(datacardname.c_str());

    for(int j = 0; j < nDatasets; j++) {
        dataSetName = datasets[j]->Name();
        cout << dataSetName << endl;
        if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
            dataSetName.find("DATA") != string::npos || dataSetName.find("JER") != string::npos ||
            dataSetName.find("JES") != string::npos || dataSetName.find("MLM") != string::npos ||
            dataSetName.find("Up") != string::npos || dataSetName.find("Scale") != string::npos ||
            dataSetName.find(otherTTbarsample) != string::npos|| dataSetName.find("TTJets_aMCatNLO")!=string::npos ||
            dataSetName.find("RareTT") != string::npos ||dataSetName.find("Down") != string::npos ||
            dataSetName.find("ISR") != string::npos || dataSetName.find("FSR") != string::npos ||
            dataSetName.find("TTUE") != string::npos) {
            continue;
        } else {
            MCdatasets.push_back(dataSetName);
            howmanyMC += 1;
        }
    }

    card << "imax " + static_cast<ostringstream*>(&(ostringstream() << nChannels))->str() + "\n";
    card << "jmax " + static_cast<ostringstream*>(&(ostringstream() << howmanyMC - 1))->str() + "\n";
    card << "kmax *\n";
    card << "---------------\n";
    card << "shapes * * " + shapefileName + "  $CHANNEL__$PROCESS__nominal  $CHANNEL__$PROCESS__$SYSTEMATIC\n";
    card << "---------------\n";
    card << "bin                               ";

    binname = channel;
    card << binname + " ";

    card << "\n";
    card << "observation                               ";

    tempEntries = 0;
    for(int j = 0; j < nDatasets; j++) {
        dataSetName = datasets[j]->Name();
        if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
            dataSetName.find("DATA") != string::npos) {
            histoName = channel + "__data_obs__nominal";
            tempHisto = (TH1F*)shapefile->Get(histoName.c_str());
            tempEntries = tempHisto->GetSumOfWeights();
            card << static_cast<ostringstream*>(&(ostringstream() << tempEntries))->str() + "         ";
        } else {
            continue;
        }
    }

    card << "\n";

    card << "---------------------------\n";
    card << "bin                               ";

    for(int i = 0; i < howmanyMC; i++)
        card << binname + "                ";

    card << "\n";
    card << "process                             ";

    for(int j = 0; j < nDatasets; j++) {
        dataSetName = datasets[j]->Name();
        if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
            dataSetName.find("DATA") != string::npos) {
            continue;
        } else if(dataSetName.find("JER") != string::npos || dataSetName.find("JES") != string::npos ||
            dataSetName.find("Up") != string::npos || dataSetName.find("Down") != string::npos ||
            dataSetName.find("RareTT") != string::npos || dataSetName.find("ISR") != string::npos ||
            dataSetName.find("FSR") != string::npos || dataSetName.find("TTUE") != string::npos ) {
            continue;
        } else if(dataSetName.find(otherTTbarsample) != string::npos || dataSetName.find("TTJets_aMCatNLO")!=string::npos) {
            continue;
        } else if(dataSetName.find(mainTTbarsample)!=string::npos){
            card<< "ttbarTTX           ";
        } else if(dataSetName.find("TTZ") != string::npos) {
            card <<"TTRARE           ";
        } else {
            card << dataSetName + "           ";
        }
    }

    card << "\n";
    card << "process                                ";

    for(int i = 0; i < howmanyMC; i++) {
        card << static_cast<ostringstream*>(&(ostringstream() << i))->str() + "                     ";
    }

    card << "\n";
    card << "rate                                ";

    tempEntries = 0;
    for(int j = 0; j < nDatasets; j++) {
        dataSetName = datasets[j]->Name();
        if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
            dataSetName.find("DATA") != string::npos) {
            continue;
        } else if(dataSetName.find("JER") != string::npos || dataSetName.find("JES") != string::npos ||
            dataSetName.find("Up") != string::npos || dataSetName.find("Down") != string::npos ||
            dataSetName.find("RareTT") != string::npos || dataSetName.find("ISR") != string::npos ||
            dataSetName.find("FSR") != string::npos || dataSetName.find("TTUE") != string::npos) {
            continue;
        } else if(dataSetName.find(otherTTbarsample) != string::npos || dataSetName.find("TTJets_aMCatNLO")!=string::npos) {
            continue;
        } else if(dataSetName.find(mainTTbarsample) != string::npos){
            histoName = channel + "__" + "ttbarTTX" + "__nominal";
            tempHisto = (TH1F*)shapefile->Get(histoName.c_str());
            tempEntries = tempHisto->GetSumOfWeights();
            card << static_cast<ostringstream*>(&(ostringstream() << tempEntries))->str() + "               ";
        } else if(dataSetName.find("TTZ") != string::npos) {
            histoName = channel + "__" + "TTRARE" + "__nominal";
            tempHisto = (TH1F*)shapefile->Get(histoName.c_str());
            tempEntries = tempHisto->GetSumOfWeights();
            card << static_cast<ostringstream*>(&(ostringstream() << tempEntries))->str() + "               ";
        } else {
            histoName = channel + "__" + dataSetName + "__nominal";
            tempHisto = (TH1F*)shapefile->Get(histoName.c_str());
            tempEntries = tempHisto->GetSumOfWeights();
            card << static_cast<ostringstream*>(&(ostringstream() << tempEntries))->str() + "               ";
        }
    }

    card << "\n";
    card << "---------------------------\n";
    card << "lumi                  lnN           ";
    for(int i = 0; i < nChannels * howmanyMC; i++) {
        card << "1.025                ";
    }
    card << "\n";

    card << "leptonSFMu                  lnN           ";
    for(int i = 0; i < nChannels * howmanyMC; i++) {
        card << "1.03               ";
    }
    card << "\n";
    card << "leptonSFEl                  lnN           ";
    for(int i = 0; i < nChannels * howmanyMC; i++) {
        card << "1.03               ";
    }
    card << "\n";

    for(int d = 0; d < howmanyMC; d++) {
        dataSetName = MCdatasets[d];
        if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
            dataSetName.find("DATA") != string::npos) {
            continue;
        } else if(dataSetName.find("JER") != string::npos || dataSetName.find("JES") != string::npos ||
            dataSetName.find("Up") != string::npos || dataSetName.find("Down") != string::npos ||
            dataSetName.find("RareTT") != string::npos || dataSetName.find("ISR") != string::npos || 
            dataSetName.find("FSR") != string::npos || dataSetName.find("TTUE") != string::npos) {
            continue;
        } else if(dataSetName.find("NP_overlay_ttttNLO") != string::npos) {
            card << "tttt_norm              lnN          ";
            for(int k = 0; k < nChannels; k++) {
                for(int dash1 = 0; dash1 < d; dash1++) {
                    card << "-                  ";
                }
                card << "0.94/1.05                    ";
                for(int dash2 = howmanyMC; dash2 > d + 1; dash2--) {
                    card << "-                  ";
                }
            }
            card << "\n";
        } else if(dataSetName.find(mainTTbarsample) != string::npos) {
            card << "TTJets_norm              lnN          ";
            for(int k = 0; k < nChannels; k++) {
                for(int dash1 = 0; dash1 < d; dash1++) {
                    card << "-                  ";
                }
                card << "0.95/1.05                    ";
                for(int dash2 = howmanyMC; dash2 > d + 1; dash2--) {
                    card << "-                  ";
                }
            }
            card << "\n";
        } else if(dataSetName.find("TTZ") != string::npos) { 
            card << "TTRARE_norm              lnN          ";
            for(int k = 0; k < nChannels; k++) {
                for(int dash1 = 0; dash1 < d; dash1++) {
                    card << "-                  ";
                }
                card << "0.95/1.05                    ";
                for(int dash2 = howmanyMC; dash2 > d + 1; dash2--) {
                    card << "-                  ";
                }
            }
            card << "\n";
        } else {
            card << dataSetName + "_norm      lnN           ";
            for(int k = 0; k < nChannels; k++) {
                for(int dash1 = 0; dash1 < d; dash1++) {
                    card << "-                  ";
                }
                card << "1.04                  ";
                for(int dash2 = howmanyMC; dash2 > d + 1; dash2--) {
                    card << "-                  ";
                }
            }
            card << "\n";
        }
    }
/*
    card << "alphaSTune                lnN           "; // applied to all MC datasets
    for(int d = 0; d < howmanyMC; d++) {
        dataSetName = MCdatasets[d];
        if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
            dataSetName.find("DATA") != string::npos) {
            card << "-                      ";
        } else {
            card << "1.15/0.86                      ";
        }
    }
    card << "\n";
    
    card << "leptonSF                lnN           "; // applied to all MC datasets
    for(int d = 0; d < howmanyMC; d++) {
        dataSetName = MCdatasets[d];
        if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
            dataSetName.find("DATA") != string::npos) {
            card << "-                      ";
        } else if(leptoAbbr.find("MuEl") != string::npos) {
            card << "1.02                      ";
        } else if(leptoAbbr.find("MuMu") != string::npos) {
            card << "1.02                      ";
        } else if(leptoAbbr.find("ElEl") != string::npos) {
            card << "1.02                      ";
        } else {
            card << "-                      ";
        }
    }
    card << "\n";
*/
    card << "ttMEScale                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else {
                 card << "-                  ";
            }
        }
    card << "\n";

    card << "TTTTMEScale                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }
            else {
                 card << "-                  ";
            }
        }

    // card << "\n";
    // card << "btag_light                shape           ";
    //  for(int d = 0; d < howmanyMC; d++) {
    //         dataSetName = MCdatasets[d];
    //         if(dataSetName.find(mainTTbarsample) != string::npos) {
    //             card << "1                  ";
    //         }
    //         else if(dataSetName.find("tttt") != string::npos) {
    //             card << "1                  ";
    //         }
    //         else {
    //              card << "-                  ";
    //         }
    //     }
    // card << "\n";
    // card << "btag_heavy                shape           ";
    //  for(int d = 0; d < howmanyMC; d++) {
    //         dataSetName = MCdatasets[d];
    //         if(dataSetName.find(mainTTbarsample) != string::npos) {
    //             card << "1                  ";
    //         }
    //         else if(dataSetName.find("tttt") != string::npos) {
    //             card << "1                  ";
    //         }
    //         else {
    //              card << "-                  ";
    //         }
    //     }
    card << "\n";
    card << "PU                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }
            else {
                 card << "-                  ";
            }
        }
    card << "\n";

    card << "TTPT                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else {
                 card << "-                  ";
            }
    }
    card << "\n";

    card << "JES                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }
            else {
                 card << "-                  ";
            }
        }
    card << "\n";

    card << "SubTotalPileUp                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }
            else {
                 card << "-                  ";
            }
        }
    card << "\n";
    card << "SubTotalRelative                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }
            else {
                 card << "-                  ";
            }
        }
    card << "\n";
    card << "SubTotalPt                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }
            else {
                 card << "-                  ";
            }
        }
    card << "\n";
    card << "SubTotalScale                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }
            else {
                 card << "-                  ";
            }
        }
    card << "\n";

    card << "JER                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }
            else {
                 card << "-                  ";
            }
        }
    card << "\n";
/*
    card << "ttGenerator                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else {
                 card << "-                  ";
            }
        }
    card << "\n";
*/
    card << "TTUE                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
    }
    card << "\n";
    card << "TTISR                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
    }
    card << "\n";
    card << "TTFSR                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
    }
    card << "\n";
    card << "TTJets_HDAMP                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
    }
    card << "TTJets_PDF                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
    }
    card << "ttttISR                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
    }
    card << "\n";
    card << "ttttFSR                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
    }
    card << "\n";
    card << "heavyFlav                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else {
                 card << "-                  ";
            }
    }
    card << "\n";
    card << "btagWeightCSVHF                shape           ";
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }            
            else {
                 card << "-                  ";
            }
        }
    card << "\n";
    card << "btagWeightCSVLF                shape           ";
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }            
            else {
                 card << "-                  ";
            }
        }
    card << "\n";
    card << "btagWeightCSVHFStats1                shape           ";
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }            
            else {
                 card << "-                  ";
            }
        }    card << "\n";
    card << "btagWeightCSVHFStats2                shape           ";
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }            
            else {
                 card << "-                  ";
            }
        }
    card << "\n";
    card << "btagWeightCSVLFStats1                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
        dataSetName = MCdatasets[d];
        if(dataSetName.find(mainTTbarsample) != string::npos) {
            card << "1                  ";
        }
        else if(dataSetName.find("tttt") != string::npos) {
            card << "1                  ";
        }            
        else {
             card << "-                  ";
        }
    }  
    card << "\n";
    card << "btagWeightCSVLFStats2                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
        dataSetName = MCdatasets[d];
        if(dataSetName.find(mainTTbarsample) != string::npos) {
            card << "1                  ";
        }
        else if(dataSetName.find("tttt") != string::npos) {
            card << "1                  ";
        }            
        else {
             card << "-                  ";
        }
    }
    card << "\n";
    card << "btagWeightCSVCFErr1                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
        dataSetName = MCdatasets[d];
        if(dataSetName.find(mainTTbarsample) != string::npos) {
            card << "1                  ";
        }
        else if(dataSetName.find("tttt") != string::npos) {
            card << "1                  ";
        }            
        else {
             card << "-                  ";
        }
    }
    card << "\n";
    card << "btagWeightCSVCFErr2                shape           ";
    for(int d = 0; d < howmanyMC; d++) {
        dataSetName = MCdatasets[d];
        if(dataSetName.find(mainTTbarsample) != string::npos) {
            card << "1                  ";
        }
        else if(dataSetName.find("tttt") != string::npos) {
            card << "1                  ";
        }            
        else {
             card << "-                  ";
        }
    }

    card << "\n";
    card << "* autoMCStats 0";
    card.close();
};

void Split_DataCardProducer(string VoI,
    TFile* shapefile,
    string shapefileName,
    string channel,
    string leptoAbbr,
    bool jetSplit,
    string sSplitVar1,
    float fbSplit1,
    float ftSplit1,
    float fwSplit1,
    string xmlNom,
    float lScale)
{
    TTreeLoader treeLoader;
    vector<Dataset*> datasets; // cout<<"vector filled"<<endl;
    const char* xmlfile = xmlNom.c_str();
    treeLoader.LoadDatasets(datasets, xmlfile); // cout<<"datasets loaded"<<endl;
    int nDatasets = datasets.size();
    TH1F* tempHisto;
    float tempEntries;
    int nChannels = 0;
    int howmanyMC = 0;
    string mainTTbarsample;
    string otherTTbarsample;
    cout << "channel  " << channel << endl;
    if(channel == "ttttmu" || channel == "ttttel") {
        mainTTbarsample = "TTJets_powheg";
        otherTTbarsample = "TTJets_MLM";
    } else {
        mainTTbarsample = "TTJetsPowheg";
        otherTTbarsample = "TTJetsMG"; 
    }
    vector<string> MCdatasets; // contains only MC samples required in datacard
    cout << "\nPRODUCING DATACARD\n" << endl;

    string numStr1, binname, histoName, dataSetName;
    ofstream card;
    std::string slScale = intToStr(lScale);
    string datacardname = "datacard" + leptoAbbr + "_" + VoI + "_JS" + ".txt";
    card.open(datacardname.c_str());
    cout << "datacard name " << datacardname << endl;
    cout << fbSplit1 << "  " << ftSplit1 << "  " << fwSplit1 << endl;
    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        nChannels += 1;
    }

    for(int j = 0; j < nDatasets; j++) {
        dataSetName = datasets[j]->Name();
        cout << dataSetName << endl;
        if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
            dataSetName.find("DATA") != string::npos || dataSetName.find("JER") != string::npos ||
            dataSetName.find("JES") != string::npos || dataSetName.find("MLM") != string::npos ||
            dataSetName.find("MEScale") != string::npos || dataSetName.find("Scale") != string::npos ||
            dataSetName.find(otherTTbarsample) != string::npos || dataSetName.find("TTJets_aMCatNLO") != string::npos ||
            dataSetName.find("TTW") != string::npos || //dataSetName.find("TTZ") != string::npos ||
            dataSetName.find("TTH") != string::npos || dataSetName.find("TTJets_SingleLept") != string::npos ||
            dataSetName.find("WW") != string::npos || dataSetName.find("WZ") != string::npos ||
            dataSetName.find("ZZ") != string::npos || dataSetName.find("ISR") != string::npos ||
            dataSetName.find("FSR") != string::npos || dataSetName.find("TTUE") != string::npos) {
            continue;
        } else {
            MCdatasets.push_back(dataSetName);
            howmanyMC += 1;
        }
    }
    cout << "howmanyMC: " << howmanyMC << endl;
    card << "imax " + static_cast<ostringstream*>(&(ostringstream() << nChannels))->str() + "\n";
    card << "jmax " + static_cast<ostringstream*>(&(ostringstream() << howmanyMC - 1))->str() +
            "\n"; // number of background (so minus data and signal)
    card << "kmax *\n";
    card << "---------------\n";
    card << "shapes * * " + shapefileName + "  $CHANNEL__$PROCESS__nominal  $CHANNEL__$PROCESS__$SYSTEMATIC\n";
    card << "---------------\n";
    card << "bin                               ";

    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        binname = channel + numStr1 + sSplitVar1;
        card << binname + " ";
    }
    card << "\n";
    card << "observation                               ";
    cout << "obs" << endl;
    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        binname = channel + numStr1 + sSplitVar1;
        tempEntries = 0;
        for(int j = 0; j < nDatasets; j++) {
            dataSetName = datasets[j]->Name();
            if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
                dataSetName.find("DATA") != string::npos) {
                histoName = channel + numStr1 + sSplitVar1 + "__data_obs__nominal";
                cout << histoName << endl;
                tempHisto = (TH1F*)shapefile->Get(histoName.c_str());
                tempEntries = tempHisto->GetSumOfWeights();
                cout << "   " << tempEntries << endl;
                card << static_cast<ostringstream*>(&(ostringstream() << tempEntries))->str() + "         ";
            } else {
                continue;
            }
        }
    }
    card << "\n";

    card << "---------------------------\n";
    card << "bin                               ";
    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        binname = channel + numStr1 + sSplitVar1;
        for(int i = 0; i < howmanyMC; i++)
            card << binname + " ";
    }
    card << "\n";
    card << "process                             ";
    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        binname = channel + numStr1 + sSplitVar1;
        for(int j = 0; j < nDatasets; j++) {
            dataSetName = datasets[j]->Name();
            if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
                dataSetName.find("DATA") != string::npos) {
                continue;
            } else if(dataSetName.find("JER") != string::npos || dataSetName.find("JES") != string::npos ||
                      dataSetName.find("Scale") != string::npos || dataSetName.find("MLM") != string::npos ||
                      dataSetName.find("TTW") != string::npos || //dataSetName.find("TTZ") != string::npos ||
                      dataSetName.find("TTH") != string::npos || dataSetName.find("TTJets_SingleLept") != string::npos ||
                      dataSetName.find("WW") != string::npos || dataSetName.find("WZ") != string::npos ||
                      dataSetName.find("ZZ") != string::npos || dataSetName.find("ISR") != string::npos ||
                      dataSetName.find("FSR") != string::npos || dataSetName.find("TTUE") != string::npos) {
                continue;
            } else if(dataSetName.find(otherTTbarsample) != string::npos ||
                dataSetName.find("TTJets_aMCatNLO") != string::npos) {
                continue;
            } else if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "TTJetsPowheg           ";
            } else if(dataSetName.find("TTZ") != string::npos) {
                card << "TTRare           ";
            } else {
                card << dataSetName + "           ";
            }
        }
    }
    cout << "process" << endl;
    card << "\n";
    card << "process                                ";
    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        for(int i = 0; i < howmanyMC; i++) {
            card << static_cast<ostringstream*>(&(ostringstream() << i))->str() + "                    ";
        }
    }
    card << "\n";
    card << "rate                                ";
    cout << "rate" << endl;
    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();

        binname = channel + numStr1 + sSplitVar1;
        tempEntries = 0;
        for(int j = 0; j < nDatasets; j++) {
            dataSetName = datasets[j]->Name();
            if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
                dataSetName.find("DATA") != string::npos) {
                continue;
            } else if(dataSetName.find("JER") != string::npos || dataSetName.find("JES") != string::npos ||
                      dataSetName.find("Scale") != string::npos || dataSetName.find("MLM") != string::npos ||
                      dataSetName.find("TTW") != string::npos || //dataSetName.find("TTZ") != string::npos ||
                      dataSetName.find("TTH") != string::npos || dataSetName.find("TTJets_SingleLept") != string::npos ||
                      dataSetName.find("WW") != string::npos || dataSetName.find("WZ") != string::npos ||
                      dataSetName.find("ZZ") != string::npos || dataSetName.find("ISR") != string::npos ||
                      dataSetName.find("FSR") != string::npos || dataSetName.find("TTUE") != string::npos) {
                continue;
            } else if(dataSetName.find(otherTTbarsample) != string::npos ||
                dataSetName.find("TTJets_aMCatNLO") != string::npos) {
                continue;
            } else if(dataSetName.find(mainTTbarsample) != string::npos) {
                histoName = channel + numStr1 + sSplitVar1 + "__" + dataSetName + "__nominal";
                tempHisto = (TH1F*)shapefile->Get(histoName.c_str());
                tempEntries = tempHisto->GetSumOfWeights();
                card << static_cast<ostringstream*>(&(ostringstream() << tempEntries))->str() + " ";
            } else if(dataSetName.find("TTZ") != string::npos) {
                histoName = channel + numStr1 + sSplitVar1 + "__" + "TTRare" + "__nominal";
                tempHisto = (TH1F*)shapefile->Get(histoName.c_str());
                tempEntries = tempHisto->GetSumOfWeights();
                card << static_cast<ostringstream*>(&(ostringstream() << tempEntries))->str() + " ";
            } else {
                histoName = channel + numStr1 + sSplitVar1 + "__" + dataSetName + "__nominal";
                tempHisto = (TH1F*)shapefile->Get(histoName.c_str());
                tempEntries = tempHisto->GetSumOfWeights();
                card << static_cast<ostringstream*>(&(ostringstream() << tempEntries))->str() + " ";
            }
        }
    }
    cout << "lumi" << endl;
    card << "\n";
    card << "---------------------------\n";
    card << "lumi                  lnN           ";
    for(int i = 0; i < nChannels * howmanyMC; i++) {
        card << "1.062                ";
    }
    card << "\n";

//    cout << "alphaSTune" << endl;
//    card << "\n";
//    card << "---------------------------\n";
//    card << "alphaSTune                  lnN           ";
//    for(int i = 0; i < nChannels * howmanyMC; i++) {
//        card << "1.15/0.86                ";
//    }
//    card << "\n";
    for(int d = 0; d < howmanyMC; d++) {
        dataSetName = MCdatasets[d];
        if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
            dataSetName.find("DATA") != string::npos) {
            continue;
        } else if(dataSetName.find("JER") != string::npos || dataSetName.find("JES") != string::npos ||
                  dataSetName.find("Scale") != string::npos || dataSetName.find("MLM") != string::npos||
                  dataSetName.find("TTW") != string::npos || //dataSetName.find("TTZ") != string::npos ||
                  dataSetName.find("TTH") != string::npos || dataSetName.find("TTJets_SingleLept") != string::npos ||
                  dataSetName.find("WW") != string::npos || dataSetName.find("WZ") != string::npos ||
                  dataSetName.find("ZZ") != string::npos || dataSetName.find("ISR") != string::npos ||
                  dataSetName.find("FSR") != string::npos || dataSetName.find("TTUE") != string::npos) {
            continue;
        } else if(dataSetName.find(otherTTbarsample) != string::npos ||
            dataSetName.find("TTJets_aMCatNLO") != string::npos) {
            continue;
        } else if(dataSetName.find("NP_overlay_tttt") != string::npos) {
            card << "tttt_norm              lnN          ";
            for(int k = 0; k < nChannels; k++) {
                for(int dash1 = 0; dash1 < d; dash1++) {
                    card << "-                  ";
                }
                card << "0.94/1.05                    ";
                for(int dash2 = howmanyMC; dash2 > d + 1; dash2--) {
                    card << "-                  ";
                }
            }
            card << "\n";
        } else if(dataSetName.find(mainTTbarsample) != string::npos) {
            card << "TTJets_norm              lnN          ";
            for(int k = 0; k < nChannels; k++) {
                for(int dash1 = 0; dash1 < d; dash1++) {
                    card << "-                  ";
                }
                card << "0.95/1.05                    ";
                for(int dash2 = howmanyMC; dash2 > d + 1; dash2--) {
                    card << "-                  ";
                }
            }
            card << "\n";
        } else if(dataSetName.find("TTZ") != string::npos) {
            card << "TTRare_norm              lnN          ";
            for(int k = 0; k < nChannels; k++) {
                for(int dash1 = 0; dash1 < d; dash1++) {
                    card << "-                  ";
                }
                card << "0.95/1.05                    ";
                for(int dash2 = howmanyMC; dash2 > d + 1; dash2--) {
                    card << "-                  ";
                }
            }
            card << "\n";
        } else {
            card << dataSetName + "_norm      lnN           ";
            for(int k = 0; k < nChannels; k++) {
                for(int dash1 = 0; dash1 < d; dash1++) {
                    card << "-                  ";
                }
                card << "1.04                      ";
                for(int dash2 = howmanyMC; dash2 > d + 1; dash2--) {
                    card << "-                  ";
                }
            }
            card << "\n";
        }
    }
    card << "leptonSF                lnN           "; // applied to all MC datasets
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
                dataSetName.find("DATA") != string::npos) {
                card << "-                      ";
            } else if(leptoAbbr.find("MuEl") != string::npos) {
                card << "1.02                      ";
            } else if(leptoAbbr.find("MuMu") != string::npos) {
                card << "1.02                      ";
            } else if(leptoAbbr.find("ElEl") != string::npos) {
                card << "1.02                      ";
            } else {
                card << "-                      ";
            }
        }
    }
    card << "\n";
    card << "ttMEScale                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
        }
    }

    card << "\n";
    card << "ttttMEScale                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
        }
    }


    // card << "\n";
    // card << "btag_light                shape           ";
    // for(int c = 0; c < nChannels; c++) {
    //     for(int d = 0; d < howmanyMC; d++) {
    //         dataSetName = MCdatasets[d];
    //         if(dataSetName.find(mainTTbarsample) != string::npos) {
    //             card << "1                  ";
    //         } else if(dataSetName.find("tttt") != string::npos) {
    //             card << "1                  ";
    //         } else {
    //             card << "-                  ";
    //         }
    //     }
    // }
    // card << "\n";
    // card << "btag_heavy                shape           ";
    // for(int c = 0; c < nChannels; c++) {
    //     for(int d = 0; d < howmanyMC; d++) {
    //         dataSetName = MCdatasets[d];
    //         if(dataSetName.find(mainTTbarsample) != string::npos) {
    //             card << "1                  ";
    //         } else if(dataSetName.find("tttt") != string::npos) {
    //             card << "1                  ";
    //         } else {
    //             card << "-                  ";
    //         }
    //     }
    // }
    card << "\n";
    card << "PU                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            } else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
        }
    }
    card << "\n";
    card << "JES                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            } else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
        }
    }
    card << "\n";
    card << "JER                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            } else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
        }
    }
    card << "\n";
/*
    card << "ttGenerator                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
        }
    }
    card << "\n";
*/
    card << "TTUE                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
        }
    }
    card << "\n";
    card << "TTISR                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
        }
    }
    card << "\n";
    card << "TTFSR                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
        }
    }
    card << "\n";
    card << "ttttISR                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
        }
    }
    card << "\n";
    card << "ttttFSR                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
        }
    }
    card << "\n";
    card << "TTJets_HDAMP                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
        }
    }
    card << "\n";

    card << "TTJets_PDF                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
        }
    }

    card << "\n";
    card << "heavyFlav                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            } else {
                card << "-                  ";
            }
        }
    }
    card << "\n";
    card << "btagWeightCSVHF                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }            
            else {
                 card << "-                  ";
            }
        }
    }

    card << "\n";
    card << "btagWeightCSVLF                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }            
            else {
                 card << "-                  ";
            }
        }
    }

    card << "\n";
    card << "btagWeightCSVHFStats1                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }            
            else {
                 card << "-                  ";
            }
        }
    }
    card << "\n";
    card << "btagWeightCSVHFStats2                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }            
            else {
                 card << "-                  ";
            }
        }
    }

    card << "\n";
    card << "btagWeightCSVLFStats1                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }            
            else {
                 card << "-                  ";
            }
        }
    }
    card << "\n";
    card << "btagWeightCSVLFStats2                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }            
            else {
                 card << "-                  ";
            }
        }
    } 
    card << "\n";
    card << "btagWeightCSVCFErr1                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }            
            else {
                 card << "-                  ";
            }
        }
    }
    card << "\n";
    card << "btagWeightCSVCFErr2                shape           ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                  ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                  ";
            }            
            else {
                 card << "-                  ";
            }
        }
    }      
    card.close();
};


void Split2_DataCardProducer(string VoI,
    TFile* shapefile,
    string shapefileName,
    string channel,
    string leptoAbbr,
    bool jetSplit,
    bool jetTagsplit,
    string sSplitVar1,
    float fbSplit1,
    float ftSplit1,
    float fwSplit1,
    string sSplitVar2,
    float fbSplit2,
    float ftSplit2,
    float fwSplit2,
    string xmlNom,
    float lScale)
{

    //ftSplit1 = 6;

    TTreeLoader treeLoader;
    vector<Dataset*> datasets; // cout<<"vector filled"<<endl;
    const char* xmlfile = xmlNom.c_str();
    treeLoader.LoadDatasets(datasets, xmlfile); // cout<<"datasets loaded"<<endl;
    int nDatasets = datasets.size();
    TH1F* tempHisto;
    float tempEntries;
    int nChannels = 0;
    int howmanyMC = 0;
    string mainTTbarsample;
    string otherTTbarsample;
    cout << "channel  " << channel << endl;
    if(channel == "ttttmu" || channel == "ttttel") {
        mainTTbarsample = "TTJets_powheg";
        otherTTbarsample = "TTJets_MLM";
    } else {
        mainTTbarsample = "TTJetsPowheg";
        otherTTbarsample = "TTJetsMG";
    }
    vector<string> MCdatasets; // contains only MC samples required in datacard
    cout << "" << endl;
    cout << "PRODUCING DATACARD" << endl;

    string numStr1, numStr2, binname, histoName, dataSetName;
    ofstream card;
    std::string slScale = intToStr(lScale);
    string datacardname = "datacard" + leptoAbbr + "_" + VoI + "_JTS" + ".txt";
    card.open(datacardname.c_str());

    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        for(int t2 = fbSplit2; t2 <= ftSplit2; t2 += fwSplit2) {
            // for(int i=0; i<datasets.size()-1; i++){
            nChannels += 1;
            //}
        }
    }
    for(int j = 0; j < nDatasets; j++) {
        dataSetName = datasets[j]->Name();
        cout << dataSetName << endl;
        if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
            dataSetName.find("DATA") != string::npos || dataSetName.find("JER") != string::npos ||
            dataSetName.find("JES") != string::npos || dataSetName.find("MLM") != string::npos ||
            dataSetName.find("Up") != string::npos || dataSetName.find("Down") != string::npos ||
            dataSetName.find(otherTTbarsample) != string::npos|| dataSetName.find("TTJets_aMCatNLO")!=string::npos ||
            dataSetName.find("Rare1TTZ") != string::npos ||
            dataSetName.find("ISR") != string::npos ||
            dataSetName.find("FSR") != string::npos || dataSetName.find("TTUE") != string::npos ||
            dataSetName.find("Rare2TTW") != string::npos || dataSetName.find("Rare2TTZ") != string::npos ||
            dataSetName.find("Rare2TTT") != string::npos || dataSetName.find("EW") != string::npos) {
            continue;
        } else {
            MCdatasets.push_back(dataSetName);
            howmanyMC += 1;
        }
    }
    cout << "howmanyMC: " << howmanyMC << endl;

    card << "imax " + static_cast<ostringstream*>(&(ostringstream() << nChannels))->str() + "\n";
    card << "jmax " + static_cast<ostringstream*>(&(ostringstream() << howmanyMC - 1))->str() + "\n";
    card << "kmax *\n";
    card << "---------------\n";
    card << "shapes * * " + shapefileName + "  $CHANNEL__$PROCESS__nominal  $CHANNEL__$PROCESS__$SYSTEMATIC\n";
    card << "---------------\n";
    card << "bin                               ";

    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        for(int t2 = fbSplit2; t2 <= ftSplit2; t2 += fwSplit2) {
            numStr2 = static_cast<ostringstream*>(&(ostringstream() << t2))->str();
            binname = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2;
            card << binname + " ";
        }
    }
    card << "\n";
    card << "observation                               ";
    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        for(int t2 = fbSplit2; t2 <= ftSplit2; t2 += fwSplit2) {
            numStr2 = static_cast<ostringstream*>(&(ostringstream() << t2))->str();
            binname = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2;
            tempEntries = 0;
            for(int j = 0; j < nDatasets; j++) {
                dataSetName = datasets[j]->Name();
                if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
                    dataSetName.find("DATA") != string::npos) {
                    histoName = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__data_obs__nominal";
                    tempHisto = (TH1F*)shapefile->Get(histoName.c_str());
                    tempEntries = tempHisto->GetSumOfWeights();
                    card << static_cast<ostringstream*>(&(ostringstream() << tempEntries))->str() + "         ";
                } else {
                    continue;
                }
            }
        }
    }
    card << "\n";

    card << "---------------------------\n";
    card << "bin                               ";
    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        for(int t2 = fbSplit2; t2 <= ftSplit2; t2 += fwSplit2) {
            numStr2 = static_cast<ostringstream*>(&(ostringstream() << t2))->str();
            binname = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2;
            for(int i = 0; i < howmanyMC; i++)
                card << binname + " ";
        }
    }
    card << "\n";
    card << "process                             ";
    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        for(int t2 = fbSplit2; t2 <= ftSplit2; t2 += fwSplit2) {
            binname = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2;
            for(int j = 0; j < nDatasets; j++) {
                dataSetName = datasets[j]->Name();
                if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
                   dataSetName.find("DATA") != string::npos || dataSetName.find("JER") != string::npos ||
                   dataSetName.find("JES") != string::npos || dataSetName.find("MLM") != string::npos ||
                   dataSetName.find("Up") != string::npos || dataSetName.find("Down") != string::npos ||
                   dataSetName.find("Rare1TTZ") != string::npos ||
                   dataSetName.find("ISR") != string::npos ||
                   dataSetName.find("FSR") != string::npos || dataSetName.find("TTUE") != string::npos ||
                   dataSetName.find("Rare2TTW") != string::npos || dataSetName.find("Rare2TTZ") != string::npos ||
                   dataSetName.find("Rare2TTT") != string::npos || dataSetName.find("EW") != string::npos) {
                    continue;
                } else if(dataSetName.find(otherTTbarsample) != string::npos|| dataSetName.find("TTJets_aMCatNLO")!=string::npos) {
                    continue;
                } else if(dataSetName.find(mainTTbarsample) != string::npos) {
                    card <<"ttbarTTX           ";
                } else if (dataSetName.find("Rare1TTH") != string::npos){
                    card <<"TTRARE           ";
                } else if (dataSetName.find("Rare2TTHH") != string::npos){
                    card <<"TTRARE_plus           ";
                } else if (dataSetName.find("DYJets") != string::npos){
                    card <<"EW           ";
                } else {
                    card << dataSetName + "           ";
                }
            }
        }
    }

    card << "\n";
    card << "process                                ";
    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        for(int t2 = fbSplit2; t2 <= ftSplit2; t2 += fwSplit2) {
            for(int i = 0; i < howmanyMC; i++) {
                card << static_cast<ostringstream*>(&(ostringstream() << i))->str() + "                    ";
            }
        }
    }
    card << "\n";
    card << "rate                                ";
    for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
        numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();
        for(int t2 = fbSplit2; t2 <= ftSplit2; t2 += fwSplit2) {
            numStr2 = static_cast<ostringstream*>(&(ostringstream() << t2))->str();
            binname = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2;
            tempEntries = 0;
            for(int j = 0; j < nDatasets; j++) {
                dataSetName = datasets[j]->Name();
                if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
                   dataSetName.find("DATA") != string::npos || dataSetName.find("JER") != string::npos ||
                   dataSetName.find("JES") != string::npos || dataSetName.find("MLM") != string::npos ||
                   dataSetName.find("Up") != string::npos || dataSetName.find("Down") != string::npos ||
                   dataSetName.find("Rare1TTZ") != string::npos ||
                   dataSetName.find("ISR") != string::npos ||
                   dataSetName.find("FSR") != string::npos || dataSetName.find("TTUE") != string::npos ||
                   dataSetName.find("Rare2TTW") != string::npos || dataSetName.find("Rare2TTZ") != string::npos ||
                   dataSetName.find("Rare2TTT") != string::npos || dataSetName.find("EW") != string::npos) {
                    continue;
                } else if(dataSetName.find(otherTTbarsample) != string::npos|| dataSetName.find("TTJets_aMCatNLO")!=string::npos) {
                    continue;
                } else if (dataSetName.find(mainTTbarsample) != string::npos){
                    histoName = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__ttbarTTX" + "__nominal";
                    tempHisto = (TH1F*)shapefile->Get(histoName.c_str());
                    tempEntries = tempHisto->GetSumOfWeights();
                    card << static_cast<ostringstream*>(&(ostringstream() << tempEntries))->str() + " ";
                } else if(dataSetName.find("Rare1TTH") != string::npos) {
                    histoName = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__TTRARE" + "__nominal";
                    tempHisto = (TH1F*)shapefile->Get(histoName.c_str());
                    tempEntries = tempHisto->GetSumOfWeights();
                    card << static_cast<ostringstream*>(&(ostringstream() << tempEntries))->str() + " ";
                } else if(dataSetName.find("Rare2TTHH") != string::npos) {
                    histoName = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__TTRARE_plus" + "__nominal";
                    tempHisto = (TH1F*)shapefile->Get(histoName.c_str());
                    tempEntries = tempHisto->GetSumOfWeights();
                    card << static_cast<ostringstream*>(&(ostringstream() << tempEntries))->str() + " ";
                } else if(dataSetName.find("DYJets") != string::npos) {
                    histoName = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__EW" + "__nominal";
                    tempHisto = (TH1F*)shapefile->Get(histoName.c_str());
                    tempEntries = tempHisto->GetSumOfWeights();
                    card << static_cast<ostringstream*>(&(ostringstream() << tempEntries))->str() + " ";
                } else {
                    histoName = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + dataSetName + "__nominal";
                    tempHisto = (TH1F*)shapefile->Get(histoName.c_str());
                    tempEntries = tempHisto->GetSumOfWeights();
                    card << static_cast<ostringstream*>(&(ostringstream() << tempEntries))->str() + " ";
                }
            }
        }
    }
    card << "\n";
    card << "---------------------------\n";
    card << "lumi			lnN			";
    for(int i = 0; i < nChannels * howmanyMC; i++) {
        card << "1.025			";
    }
    card << "\n";

    card << "leptonSFMu		lnN			";
    for(int i = 0; i < nChannels * howmanyMC; i++) {
        card << "1.03			";
    }
    card << "\n";
    card << "leptonSFEl		lnN			";
    for(int i = 0; i < nChannels * howmanyMC; i++) {
        card << "1.03			";
    }
    card << "\n";
    //card << "leptontrigSF                  lnN           ";
    //for(int i = 0; i < nChannels * howmanyMC; i++) {
    //    card << "1.02               ";
    //}
    //card << "\n";

    // cout << "alphaSTune" << endl;
    // card << "\n";
    // card << "---------------------------\n";
    // card << "alphaSTune                  lnN           ";
    // for(int i = 0; i < nChannels * howmanyMC; i++) {
    //     card << "1.15/0.86                ";
    // }
    // card << "\n";
    for(int d = 0; d < howmanyMC; d++) {
        dataSetName = MCdatasets[d];
        if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
           dataSetName.find("DATA") != string::npos || dataSetName.find("JER") != string::npos ||
           dataSetName.find("JES") != string::npos || dataSetName.find("MLM") != string::npos ||
           dataSetName.find("Up") != string::npos || dataSetName.find("Down") != string::npos ||
           dataSetName.find("Rare1TTZ") != string::npos ||
           dataSetName.find("ISR") != string::npos ||
           dataSetName.find("FSR") != string::npos || dataSetName.find("TTUE") != string::npos ||
           dataSetName.find("Rare2TTW") != string::npos || dataSetName.find("Rare2TTZ") != string::npos ||
           dataSetName.find("Rare2TTT") != string::npos || dataSetName.find("EW") != string::npos) {
            continue;
        } else if(dataSetName.find(otherTTbarsample) != string::npos|| dataSetName.find("TTJets_aMCatNLO")!=string::npos) {
            continue;

        } else if(dataSetName.find("NP_overlay_ttttNLO") != string::npos) {
            card << "tttt_norm		lnN			";
            for(int k = 0; k < nChannels; k++) {
                for(int dash1 = 0; dash1 < d; dash1++) {
                    card << "-			";
                }
                card << "0.94/1.05		";
                for(int dash2 = howmanyMC; dash2 > d + 1; dash2--) {
                    card << "-			";
                }
            }
            card << "\n";

        } else if(dataSetName.find(mainTTbarsample) != string::npos) {
            card << "TTJets_norm		lnN			";
            for(int k = 0; k < nChannels; k++) {
                for(int dash1 = 0; dash1 < d; dash1++) {
                    card << "-			";
                }
                card << "0.95/1.05		";
                for(int dash2 = howmanyMC; dash2 > d + 1; dash2--) {
                    card << "-			";
                }
            }
            card << "\n";

        } else if(dataSetName.find("Rare1TTH") != string::npos) {
            card << "TTRARE_norm		lnN			";
            for(int k = 0; k < nChannels; k++) {
                for(int dash1 = 0; dash1 < d; dash1++) {
                    card << "-			";
                }
                card << "1.50			";
                for(int dash2 = howmanyMC; dash2 > d + 1; dash2--) {
                    card << "-			";
                }
            }
            card << "\n";
/*
        } else if(dataSetName.find("Rare1TTZ") != string::npos) {
            card << "TTZ_norm                lnN                     ";
            for(int k = 0; k < nChannels; k++) {
                for(int dash1 = 0; dash1 < d; dash1++) {
                    card << "-                  ";
                }
                card << "1.50                   ";
                for(int dash2 = howmanyMC; dash2 > d + 1; dash2--) {
                    card << "-                  ";
                }
            }
            card << "\n";
*/
        } else if(dataSetName.find("Rare2TTHH") != string::npos) {
            card << "TTRARE_plus_norm	lnN                     ";
            for(int k = 0; k < nChannels; k++) {
                for(int dash1 = 0; dash1 < d; dash1++) {
                    card << "-                       ";
                }
                card << "1.50                   ";
                for(int dash2 = howmanyMC; dash2 > d + 1; dash2--) {
                    card << "-                        ";
                }
            }
            card << "\n";

        } else if(dataSetName.find("DYJets") != string::npos) {
            card << "EW			lnN                     ";
            for(int k = 0; k < nChannels; k++) {
                for(int dash1 = 0; dash1 < d; dash1++) {
                    card << "-                       ";
                }
                card << "1.04                    ";
                for(int dash2 = howmanyMC; dash2 > d + 1; dash2--) {
                    card << "-                       ";
                }
            }
            card << "\n";

        } else {
            card << dataSetName + "_norm		lnN			";
            for(int k = 0; k < nChannels; k++) {
                for(int dash1 = 0; dash1 < d; dash1++) {
                    card << "-			";
                }
                card << "1.04			";
                for(int dash2 = howmanyMC; dash2 > d + 1; dash2--) {
                    card << "-			";
                }
            }
            card << "\n";
        }
    }

    card << "ttMEScale		shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else {
                 card << "-			";
            }
        }
    }
    card << "\n";

    card << "TTTTMEScale		shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find("tttt") != string::npos) {
                card << "1			";
            }
            else {
                 card << "-			";
            }
        }
    }
    card << "\n";

    card << "PU			shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1			";
            }
            else {
                 card << "-			";
            }
        }
    }
    card << "\n";

    card << "TTPT			shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else {
                card << "-			";
            }
        }
    }
    card << "\n";

    card << "SFjetnorm		shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else {
                 card << "-			";
            }
        }
    }
    card << "\n";
/*
    card << "JES			shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1			";
            }
            else {
                 card << "-			";
            }
        }
    }
    card << "\n";
*/
    card << "SubTotalPileUp		shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1			";
            }
            else {
                 card << "-			";
            }
        }
    }
    card << "\n";

    card << "SubTotalRelative	shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1			";
            }
            else {
                 card << "-			";
            }
        }
    }
    card << "\n";

    card << "SubTotalPt		shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1			";
            }
            else {
                 card << "-			";
            }
        }
    }
    card << "\n";

    card << "SubTotalScale		shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1			";
            }
            else {
                 card << "-			";
            }
        }
    }
    card << "\n";

    card << "SubTotalFlavor		shape                   ";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                       ";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1                       ";
            }
            else {
                card << "-                       ";
            }
        }
    }
    card << "\n";

    card << "JER			shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1			";
            }
            else {
                 card << "-			";
            }
        }
    }
    card << "\n";

    card << "TTUE			lnN			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                //card << "1                      ";
                    if(channel == "ttttmumu"){
			if(c==0) card << "1.04264			";
                        if(c==1) card << "1.21131			";
                        if(c==2) card << "1.18877			";
                        if(c==3) card << "1.26095			";
                        if(c==4) card << "1.5362			";
                        if(c==5) card << "1.30113			";
		    }
                    if(channel == "ttttmuel"){ 
                        if(c==0) card << "1.09384			";
                        if(c==1) card << "1.04363			";
                        if(c==2) card << "1.15548			";
                        if(c==3) card << "1.20391			";
                        if(c==4) card << "1.24988			";
                        if(c==5) card << "1.48636			";
                    }
                    if(channel == "ttttelel"){ 
                        if(c==0) card << "1.04198			";
                        if(c==1) card << "1.0308			";
                        if(c==2) card << "1.25708			";
                        if(c==3) card << "1.18569			";
                        if(c==4) card << "1.30273			";
                        if(c==5) card << "1.35435			";
                    }
		    if(channel == "comb"){
                        if(c==0) card << "1.06828                       ";
                        if(c==1) card << "1.07895                       ";
                        if(c==2) card << "1.19784                       ";
                        if(c==3) card << "1.19905                       ";
                        if(c==4) card << "1.35313                       ";
                        if(c==5) card << "1.2789                       ";
                    }
            } else {
                card << "-			";
            }
        }
    }
    card << "\n";

    card << "TTISR			lnN			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                //card << "1                      ";
                    if(channel == "ttttmumu"){ 
                        if(c==0) card << "1.08842			";
                        if(c==1) card << "1.02827			";
                        if(c==2) card << "1.3042			";
                        if(c==3) card << "1.33182			";
                        if(c==4) card << "1.34923			";
                        if(c==5) card << "1.38094			";
                    }
                    if(channel == "ttttmuel"){ 
                        if(c==0) card << "1.06986			";
                        if(c==1) card << "1.12765			";
                        if(c==2) card << "1.28189			";
                        if(c==3) card << "1.2821			";
                        if(c==4) card << "1.4454			";
                        if(c==5) card << "1.67303			";
                    }
                    if(channel == "ttttelel"){ 
                        if(c==0) card << "1.08159			";
                        if(c==1) card << "1.03154			";
                        if(c==2) card << "1.36645			";
                        if(c==3) card << "1.38621			";
                        if(c==4) card << "1.2716			";
                        if(c==5) card << "1.37747			";
                    }
                    if(channel == "comb"){
                        if(c==0) card << "1.08122                       ";
                        if(c==1) card << "1.07522                       ";
                        if(c==2) card << "1.31954                       ";
                        if(c==3) card << "1.33439                       ";
                        if(c==4) card << "1.40456                       ";
                        if(c==5) card << "1.5383                       ";
                    }
            } else {
                card << "-			";
            }
        }
    }
    card << "\n";

    card << "TTFSR			lnN			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                //card << "1                      ";
                    if(channel == "ttttmumu"){ 
                        if(c==0) card << "1.20644			";
                        if(c==1) card << "1.11909			";
                        if(c==2) card << "1.23585			";
                        if(c==3) card << "1.09814			";
                        if(c==4) card << "1.26624			";
                        if(c==5) card << "1.16334			";
                    }
                    if(channel == "ttttmuel"){ 
                        if(c==0) card << "1.15613			";
                        if(c==1) card << "1.15487			";
                        if(c==2) card << "1.24328			";
                        if(c==3) card << "1.20757			";
                        if(c==4) card << "1.35274			";
                        if(c==5) card << "1.19785			";
                    }
                    if(channel == "ttttelel"){ 
                        if(c==0) card << "1.13159			";
                        if(c==1) card << "1.07311			";
                        if(c==2) card << "1.26272			";
                        if(c==3) card << "1.20014			";
                        if(c==4) card << "1.28903			";
                        if(c==5) card << "1.48496		";
                    }
                    if(channel == "comb"){
                        if(c==0) card << "1.16836                       ";
                        if(c==1) card << "1.10803                       ";
                        if(c==2) card << "1.25985                       ";
                        if(c==3) card << "1.18267                       ";
                        if(c==4) card << "1.32605                       ";
                        if(c==5) card << "1.06899                       ";
                    }
            } else {
                card << "-			";
            }
        }
    }
    card << "\n";

    card << "TTJets_HDAMP		lnN			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
               // card << "1                      ";
                    if(channel == "ttttmumu"){ 
                        if(c==0) card << "1.09054			";
                        if(c==1) card << "1.08724			";
                        if(c==2) card << "1.08472			";
                        if(c==3) card << "1.08662			";
                        if(c==4) card << "1.07647			";
                        if(c==5) card << "1.11115			";
                    }
                    if(channel == "ttttmuel"){ 
                        if(c==0) card << "1.08857			";
                        if(c==1) card << "1.08303			";
                        if(c==2) card << "1.0866			";
                        if(c==3) card << "1.09413			";
                        if(c==4) card << "1.08403			";
                        if(c==5) card << "1.09257			";
                    }
                    if(channel == "ttttelel"){ 
                        if(c==0) card << "1.08708			";
                        if(c==1) card << "1.10308			";
                        if(c==2) card << "1.10035			";
                        if(c==3) card << "1.08738			";
                        if(c==4) card << "1.08961			";
                        if(c==5) card << "1.08559			";
                    }
                    if(channel == "comb"){
                        if(c==0) card << "1.09166                       ";
                        if(c==1) card << "1.0911                       ";
                        if(c==2) card << "1.09253                       ";
                        if(c==3) card << "1.09351                       ";
                        if(c==4) card << "1.08708                       ";
                        if(c==5) card << "1.09697                       ";
                    }
            } else {
                card << "-			";
            }
        }
    }
    card << "\n";

    card << "TTJets_PDF		shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            } else {
                card << "-			";
            }
        }
    }
    card << "\n";

    card << "TTTTISR			lnN			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find("tttt") != string::npos) {
                //card << "1                      ";
                    if(channel == "ttttmumu"){ 
                        if(c==0) card << "1.09294			";
                        if(c==1) card << "1.06523			";
                        if(c==2) card << "1.12732			";
                        if(c==3) card << "1.092			";
                        if(c==4) card << "1.06717			";
                        if(c==5) card << "1.14301			";
                    }
                    if(channel == "ttttmuel"){ 
                        if(c==0) card << "1.11894			";
                        if(c==1) card << "1.08827			";
                        if(c==2) card << "1.05489			";
                        if(c==3) card << "1.05229			";
                        if(c==4) card << "1.12955			";
                        if(c==5) card << "1.12502			";
                    }
                    if(channel == "ttttelel"){ 
                        if(c==0) card << "1.10444			";
                        if(c==1) card << "1.12573			";
                        if(c==2) card << "1.08753			";
                        if(c==3) card << "1.05848			";
                        if(c==4) card << "1.0762			";
                        if(c==5) card << "1.09262			";
                    }
                    if(channel == "comb"){
                        if(c==0) card << "1.10257                       ";
                        if(c==1) card << "1.0395                       ";
                        if(c==2) card << "1.01899                       ";
                        if(c==3) card << "1.04586                       ";
                        if(c==4) card << "1.07774                       ";
                        if(c==5) card << "1.06359                       ";
                    }
            } else {
                card << "-			";
            }
        }
    }
    card << "\n";

    card << "TTTTFSR			lnN			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find("tttt") != string::npos) {
                //card << "1                      ";
                    if(channel == "ttttmumu"){ 
                        if(c==0) card << "1.02357			";
                        if(c==1) card << "1.03794			";
                        if(c==2) card << "1.06037			";
                        if(c==3) card << "1.18839			";
                        if(c==4) card << "1.05374			";
                        if(c==5) card << "1.11733			";
                    }
                    if(channel == "ttttmuel"){ 
                        if(c==0) card << "1.02775			";
                        if(c==1) card << "1.19047			";
                        if(c==2) card << "1.13867			";
                        if(c==3) card << "1.15082			";
                        if(c==4) card << "1.11617			";
                        if(c==5) card << "1.20595			";
                    }
                    if(channel == "ttttelel"){ 
                        if(c==0) card << "1.08771			";
                        if(c==1) card << "1.14338			";
                        if(c==2) card << "1.02503			";
                        if(c==3) card << "1.22201			";
                        if(c==4) card << "1.18696			";
                        if(c==5) card << "1.09808			";
                    }
                    if(channel == "comb"){
                        if(c==0) card << "1.01101                       ";
                        if(c==1) card << "1.10631                       ";
                        if(c==2) card << "1.05903                       ";
                        if(c==3) card << "1.12752                       ";
                        if(c==4) card << "1.09199                       ";
                        if(c==5) card << "1.15689                       ";
                    }
            } else {
                card << "-			";
            }
        }
    }
    card << "\n";
    
    card << "heavyFlav		shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else {
                 card << "-			";
            }
        }
    }
    card << "\n";

    card << "btagWeightCSVHF		shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1			";
            }            
            else {
                 card << "-			";
            }
        }
    }

    card << "\n";
    card << "btagWeightCSVLF		shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1			";
            }            
            else {
                 card << "-			";
            }
        }
    }

    card << "\n";
    card << "btagWeightCSVHFStats1	shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1			";
            }            
            else {
                 card << "-			";
            }
        }
    }
    card << "\n";
    card << "btagWeightCSVHFStats2	shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1			";
            }            
            else {
                 card << "-			";
            }
        }
    }

    card << "\n";
    card << "btagWeightCSVLFStats1	shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1			";
            }            
            else {
                 card << "-			";
            }
        }
    }
    card << "\n";
    card << "btagWeightCSVLFStats2	shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1			";
            }            
            else {
                 card << "-			";
            }
        }
    } 
    card << "\n";
    card << "btagWeightCSVCFErr1	shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1			";
            }            
            else {
                 card << "-			";
            }
        }
    }
    card << "\n";
    card << "btagWeightCSVCFErr2	shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1			";
            }
            else if(dataSetName.find("tttt") != string::npos) {
                card << "1			";
            }            
            else {
                 card << "-			";
            }
        }
    }        
    
    card << "\n";
    card << "* autoMCStats 0";
    card.close();
};

std::string intToStr(int number)
{
    std::ostringstream buff;
    buff << number;
    return buff.str();
}

std::string plotVarNames(string s)
{
    string rs;
    if(s.find("BDT") != std::string::npos && s.find("trijet") == std::string::npos )
        rs = "BDT";
    else if(s.find("nJets") != std::string::npos)
        rs = "N_{j}";
    else if(s.find("SumJetMass") != std::string::npos)
        rs = "M^{H}_{Re}";
    else if(s.find("topness") != std::string::npos)
        rs = "BDT_{trijet1}";
    else if(s.find("angleBestTopAllJetCorrect") != std::string::npos)
        rs = "T";
    else if(s.find("BDT_trijet2") != std::string::npos)
        rs = "BDT_{trijet2}";
    else if(s.find("EventSph") != std::string::npos)
        rs = "S";
    else if(s.find("HT2M") != std::string::npos)
        rs = "H_{T}^{2M}";
    else if(s.find("fnjetW") != std::string::npos)
        rs = "N_{j}^{W}";
    else if(s.find("njetW") != std::string::npos)
        rs = "N_{j}^{W}";
    else if(s.find("HT") != std::string::npos && s.find("HTRat") == std::string::npos &&
            s.find("HTb") == std::string::npos && s.find("HTH") == std::string::npos &&
            s.find("HTX") == std::string::npos && s.find("HT2M") == std::string::npos)
        rs = "H_{T}";
    else if(s.find("LeadingLepPt") != std::string::npos && s.find("SubLeadingLepPt") == std::string::npos)
        rs = "p_{T}^{l1}";
    else if(s.find("HTX") != std::string::npos)
        rs = "HT_{X}";
    else if(s.find("LeadingLepEta") != std::string::npos)
        rs = "#eta^{l1}";
    else if(s.find("SubLeadingLepPt") != std::string::npos)
        rs = "p_{T}^{l2}";
    else if(s.find("dRLep") != std::string::npos)
        rs = "dR_{ll}";
    else if(s.find("HTH") != std::string::npos)
        rs = "C";
    else if(s.find("HTRat") != std::string::npos)
        rs = "H_{T}^{Rat}";
    else if(s.find("HTb") != std::string::npos)
        rs = "H_{T}^{b}";
    else if(s.find("dRbb") != std::string::npos)
        rs = "dR_{bb}";
    else if(s.find("nLtags") != std::string::npos)
        rs = "N_{tags}^{L}";
    else if(s.find("nMtags") != std::string::npos)
        rs = "N_{tags}^{M}";
    else if(s.find("nTtags") != std::string::npos)
        rs = "N_{tags}^{T}";
    else if(s.find("3rdJetPt") != std::string::npos)
        rs = "p_{T}^{Jet3}";
    else if(s.find("4thJetPt") != std::string::npos)
        rs = "p_{T}^{Jet4}";
    else if(s.find("1stJetPt") != std::string::npos)
        rs = "p_{T}^{Jet1}";
    else if(s.find("2ndJetPt") != std::string::npos)
        rs = "p_{T}^{Jet2}";
    else if(s.find("bestTopPt") != std::string::npos)
        rs = "p_{T trijet1}";
    else if(s.find("LeadingLepPhi") != std::string::npos && s.find("SubLeadingLepPhi") == std::string::npos)
        rs = "#phi_{l1}";
    else if(s.find("SubLeadingLepPhi") != std::string::npos)
        rs = "#phi_{l2}";
    else if(s.find("1stJetPhi") != std::string::npos)
        rs = "#phi_{Jet1}";
    else if(s.find("SubLeadingLepIso") != std::string::npos)
        rs = "Iso_{l2}";
    else if(s.find("LeadingLepIso") != std::string::npos && s.find("SubLeadingLepIso") == std::string::npos)
        rs = "Iso_{l1}";
    else
        rs = s;

    cout<<rs<<endl;
    return rs;
}
float findmax(float a, float b, float c){
    float tempvalue = 1.;
    if(tempvalue < a) tempvalue = a;
    if(tempvalue < b) tempvalue = b;
    return tempvalue;
}
float findmin(float a, float b, float c){
    float tempvalue = 1.;
    if(tempvalue > a) tempvalue = a;
    if(tempvalue > b) tempvalue = b;
    return tempvalue;
}

//     rs = "BDT";
// else if(s.find("nJets") != std::string::npos)
//     rs = "N_{j}";
// else if(s.find("topness") != std::string::npos)
//     rs = "BDT_{trijet1}";
// else if(s.find("EventSph") != std::string::npos)
//     rs = "S";
// else if(s.find("HT2M") != std::string::npos)
//     rs = "H_{T}^{2M}";
// else if(s.find("fnjetW") != std::string::npos)
//     rs = "N_{j}^{W}";
// else if(s.find("HT") != std::string::npos && s.find("HTRat") == std::string::npos && s.find("HTb") ==
// std::string::npos && s.find("HTH") == std::string::npos  && s.find("HT2M") == std::string::npos)
//     rs = "H
