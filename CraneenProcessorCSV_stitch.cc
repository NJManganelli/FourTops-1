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
            } else {
                cout << "!!!!!!! wrong arguments !!!" << endl;
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

                string MEScaleFileDir = "ScaleFiles" + leptoAbbr + "_light";
                mkdir(MEScaleFileDir.c_str(), 0777);
                TFile* errorfile = new TFile(("ScaleFiles" + leptoAbbr + "_light/Error" + VoI + ".root").c_str(), "RECREATE");

                child2->QueryFloatAttribute("lBound", &lBound);
                child2->QueryFloatAttribute("uBound", &uBound);
                child2->QueryIntAttribute("nBins", &NumberOfBins);
                Units = child2->Attribute("units");
                cout << "Variable : " << ppText << "  lBound : " << lBound << "   uBound : " << uBound << "  nBins: " << NumberOfBins << endl;
                
                if(jetTagsplit) {

                    Split2DatasetPlotter(NumberOfBins, lumiScale, lBound, uBound, leptoAbbr, shapefile, errorfile,
                        channel, VoI, splitVar1, bSplit1, tSplit1, wSplit1, splitVar2, bSplit2, tSplit2, wSplit2,
                        xmlFileName, CraneenPath, shapefileName, Units);
                    //if(VoI.find("BDT") != string::npos || VoI == "HT") {
                    Split2_DataCardProducer(VoI, shapefile, shapefileName, channel, leptoAbbr, jetSplit,
                        jetTagsplit, splitVar1, bSplit1, tSplit1, wSplit1, splitVar2, bSplit2, tSplit2, wSplit2,
                        xmlFileName, lumiScale);
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
    cout << " DONE !! " << endl;
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
            
            histo1D[("weightPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = 
                new TH1F(("Plus_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "Plus_tt", nBins, plotLow, plotHigh);
            histo1D[("weightMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = 
                new TH1F(("Minus_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "Minus_tt", nBins, plotLow, plotHigh);
            
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

                    if(binContentMin > histo1D[weightHistoName]->GetBinContent(binN))
                        binContentMin = histo1D[weightHistoName]->GetBinContent(binN);
                    if(binContentMax < histo1D[weightHistoName]->GetBinContent(binN))
                        binContentMax = histo1D[weightHistoName]->GetBinContent(binN);

                }
                histo1D[("weightPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->SetBinContent(binN, binContentMax);
                histo1D[("weightMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->SetBinContent(binN, binContentMin);
            }

            shapefile->cd();
            string MEScalesysname = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__ttbarTTX__ttMEScale";

            histo1D[("weightMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "Down").c_str());
            histo1D[("weightPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "Up").c_str());
            cout << "wrote sys MEScale shapes in shapefile" << endl;
        }
    }
}


void GetScaleEnvelopeSplit2_filtered(int nBins,
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
            
            histo1D[("weightPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = 
                new TH1F(("Plus_tt_f" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "Plus_tt_f", nBins, plotLow, plotHigh);
            histo1D[("weightMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = 
                new TH1F(("Minus_tt_f" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "Minus_tt_f", nBins, plotLow, plotHigh);
            
            histo1D[("weight0_tt_f" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("f_Genweight_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight1_tt_f" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("f_weight1_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight2_tt_f" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("f_weight2_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight3_tt_f" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("f_weight3_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight4_tt_f" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("f_weight4_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight5_tt_f" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("f_weight5_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight6_tt_f" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("f_weight6_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight7_tt_f" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("f_weight7_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
            histo1D[("weight8_tt_f" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                (TH1F*)shapefile->Get(("f_weight8_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());

            cout << "Got weights" << endl;

            for(int binN = 1; binN < nBins + 1; ++binN) {
                float binContentMax = -1, binContentMin = 1000000000000000;

                for(int weightIt = 1; weightIt < 9; ++weightIt) {
                    if(weightIt == 6 || weightIt == 8) {
                        continue; // extreme weights with 1/2u and 2u
                    }

                    string weightStr = static_cast<ostringstream*>(&(ostringstream() << weightIt))->str();
                    string weightHistoName = ("weight" + weightStr + "_tt_f" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str();

                    if(binContentMin > histo1D[weightHistoName]->GetBinContent(binN))
                        binContentMin = histo1D[weightHistoName]->GetBinContent(binN);
                    if(binContentMax < histo1D[weightHistoName]->GetBinContent(binN))
                        binContentMax = histo1D[weightHistoName]->GetBinContent(binN);

                }
                histo1D[("weightPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->SetBinContent(binN, binContentMax);
                histo1D[("weightMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->SetBinContent(binN, binContentMin);
            }

            shapefile->cd();
            string MEScalesysname = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__ttbarTTX_f__ttMEScale";

            histo1D[("weightMinus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "Down").c_str());
            histo1D[("weightPlus" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "Up").c_str());
            cout << "wrote sys MEScale shapes in shapefile" << endl;
        }
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
    string newTTbarSample;
    string otherTTbarsample;
    cout << "channel  " << channel << endl;
    string chanText;
    cout << "channel  " << channel << endl;
    if(channel == "ttttmu" || channel == "ttttel") {
        mainTTbarSample = "TTJets_powheg";
        otherTTbarsample = "TTJets_MLM";
    } else {
        mainTTbarSample = "TTJetsPowheg";
        newTTbarSample = "TTJetsPowheg_f";
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
            MSPlot[plotname.c_str()]->setMinLogY(0.001);
            histo1D[("TTJets_Rare"+plotname).c_str()] = new TH1F(("TTJets_Rare"+plotname).c_str(), ("TTJets_Rare"+plotname).c_str(), nBins, plotLow, plotHigh);
            histo1D[("TTJets_Rare_plus"+plotname).c_str()] = new TH1F(("TTJets_Rare_plus"+plotname).c_str(), ("TTJets_Rare_plus"+plotname).c_str(), nBins, plotLow, plotHigh);
            histo1D[("EW"+plotname).c_str()] = new TH1F(("EW"+plotname).c_str(), ("EW"+plotname).c_str(), nBins, plotLow, plotHigh);
        }
    }


    plotname = "";

    // //***********************************************OPEN FILES & GET NTUPLES**********************************************
    
    string dataSetName, filepath, histoName;
    int nEntries = 0;
    float NormFactor = 1, varofInterest, splitVar1, splitVar2,
          GenWeight = 1, weight1 = 1, weight2 = 1, weight3 = 1, weight4 = 1, weight5 = 1, weight6 = 1, weight7 = 1, weight8 = 1,
          ttbar_flav = 1, SFtrigger = 1, SFlepton = 1, SFtrigger_up = 1, SFtrigger_down = 1, SFPU = 1, SFPU_up = 1, SFPU_down = 1, SFTopPt = 1, SFTopPt_up = 1, SFTopPt_down = 1,
          SFalphaTune = 1, SFbtagCSV = 1, hdamp_up = 1, hdamp_down = 1,
          btagWeightCSVLFUp = 1, btagWeightCSVLFDown = 1, btagWeightCSVHFUp = 1,
          btagWeightCSVHFDown = 1, btagWeightCSVHFStats1Up = 1, btagWeightCSVHFStats1Down = 1,
          btagWeightCSVHFStats2Up = 1, btagWeightCSVHFStats2Down = 1, btagWeightCSVLFStats1Up = 1,
          btagWeightCSVLFStats1Down = 1, btagWeightCSVLFStats2Up = 1, btagWeightCSVLFStats2Down = 1,
          btagWeightCSVCFErr1Up = 1, btagWeightCSVCFErr1Down = 1, btagWeightCSVCFErr2Up = 1,
          btagWeightCSVCFErr2Down = 1, weight_ct10 = 1, weight_mmht14 = 1, ttXrew = 1, ttXrew_up = 1, ttXrew_down = 1,
          lepiso1, lepiso2, genHT, n_genjets, n_genleps;

    for(int d = 0; d < datasets.size(); d++){

        dataSetName = datasets[d]->Name(); 
        bool isData = false;
        if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos || dataSetName.find("DATA") != string::npos) {
            isData = true;
        }

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
        nTuple[dataSetName.c_str()]->SetBranchAddress("LeadingLepIso", &lepiso1);
        nTuple[dataSetName.c_str()]->SetBranchAddress("SubLeadingLepIso", &lepiso2);
        if(!isData){
            nTuple[dataSetName.c_str()]->SetBranchAddress("genHT", &genHT);
            nTuple[dataSetName.c_str()]->SetBranchAddress("n_genjets", &n_genjets);
            nTuple[dataSetName.c_str()]->SetBranchAddress("n_genleps", &n_genleps);
        }
        nTuple[dataSetName.c_str()]->SetBranchAddress(sSplitVar1.c_str(), &splitVar1);
        nTuple[dataSetName.c_str()]->SetBranchAddress(sSplitVar2.c_str(), &splitVar2);


        float eqlumi = 1. / datasets[d]->EquivalentLumi();
        cout << "eqlumi: " << eqlumi << endl;

        // for fixed bin width
        for(int s = fbSplit1; s <= ftSplit1; s += fwSplit1) {
            numStr1 = static_cast<ostringstream*>(&(ostringstream() << s))->str();
            for(int t2 = fbSplit2; t2 <= ftSplit2; t2 += fwSplit2) {
                numStr2 = static_cast<ostringstream*>(&(ostringstream() << t2))->str();
                histoName = dataSetName + numStr1 + sSplitVar1 + numStr2 + sSplitVar2;
                histo1D[histoName.c_str()] = new TH1F(histoName.c_str(), histoName.c_str(), nBins, plotLow, plotHigh);
                if(dataSetName.find(mainTTbarSample) != string::npos && dataSetName.find(newTTbarSample) == string::npos && dataSetName.find("JES") == string::npos &&
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

                else if(dataSetName.find(newTTbarSample) != string::npos && dataSetName.find("JES") == string::npos &&
                   dataSetName.find("JER") == string::npos && dataSetName.find("Up") == string::npos && dataSetName.find("Down") == string::npos) {
                    histo1D[("f_Genweight_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_Genweight_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_Genweight",
                            nBins, plotLow, plotHigh);
                    histo1D[("f_weight1_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_weight1_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_weight1", nBins,
                            plotLow, plotHigh);
                    histo1D[("f_weight2_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_weight2_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_weight2", nBins,
                            plotLow, plotHigh);
                    histo1D[("f_weight3_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_weight3_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_weight3", nBins,
                            plotLow, plotHigh);
                    histo1D[("f_weight4_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_weight4_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_weight4", nBins,
                            plotLow, plotHigh);
                    histo1D[("f_weight5_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_weight5_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_weight5", nBins,
                            plotLow, plotHigh);
                    histo1D[("f_weight6_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_weight6_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_weight6", nBins,
                            plotLow, plotHigh);
                    histo1D[("f_weight7_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_weight7_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_weight7", nBins,
                            plotLow, plotHigh);
                    histo1D[("f_weight8_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_weight8_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_weight8", nBins,
                            plotLow, plotHigh);
                    histo1D[("f_PU_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_PU_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_PU_Up", nBins,
                            plotLow, plotHigh);
                    histo1D[("f_PU_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_PU_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_PU_Down", nBins,
                            plotLow, plotHigh);
                    histo1D[("f_TTPT_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_TTPT_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_TTPT_Up", nBins,
                            plotLow, plotHigh);
                    histo1D[("f_TTPT_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_TTPT_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_TTPT_Down", nBins,
                            plotLow, plotHigh);
                    histo1D[("f_heavyFlav_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_heavyFlav_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_heavyFlav_Up",
                            nBins, plotLow, plotHigh);
                    histo1D[("f_heavyFlav_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_heavyFlav_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_heavyFlav_Down",
                            nBins, plotLow, plotHigh);
                    histo1D[("f_btagWeightCSVLF_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_btagWeightCSVLF_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), 
                            ("f_btagWeightCSVLF_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("f_btagWeightCSVLF_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_btagWeightCSVLF_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("f_btagWeightCSVLF_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("f_btagWeightCSVHF_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_btagWeightCSVHF_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("f_btagWeightCSVHF_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("f_btagWeightCSVHF_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_btagWeightCSVHF_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("f_btagWeightCSVHF_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("f_btagWeightCSVHFStats1_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_btagWeightCSVHFStats1_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("f_btagWeightCSVHFStats1_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("f_btagWeightCSVHFStats1_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_btagWeightCSVHFStats1_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("f_btagWeightCSVHFStats1_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("f_btagWeightCSVHFStats2_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_btagWeightCSVHFStats2_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("f_btagWeightCSVHFStats2_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("f_btagWeightCSVHFStats2_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_btagWeightCSVHFStats2_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("f_btagWeightCSVHFStats2_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("f_btagWeightCSVLFStats1_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_btagWeightCSVLFStats1_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("f_btagWeightCSVLFStats1_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("f_btagWeightCSVLFStats1_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_btagWeightCSVLFStats1_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("f_btagWeightCSVLFStats1_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("f_btagWeightCSVLFStats2_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_btagWeightCSVLFStats2_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("f_btagWeightCSVLFStats2_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("f_btagWeightCSVLFStats2_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_btagWeightCSVLFStats2_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("f_btagWeightCSVLFStats2_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("f_btagWeightCSVCFErr1_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_btagWeightCSVCFErr1_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("f_btagWeightCSVCFErr1_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("f_btagWeightCSVCFErr1_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_btagWeightCSVCFErr1_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("f_btagWeightCSVCFErr1_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("f_btagWeightCSVCFErr2_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_btagWeightCSVCFErr2_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("f_btagWeightCSVCFErr2_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);
                    histo1D[("f_btagWeightCSVCFErr2_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_btagWeightCSVCFErr2_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(),
                            ("f_btagWeightCSVCFErr2_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), nBins, plotLow, plotHigh);  
                    histo1D[("f_hdamp_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_hdamp_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_hdamp_Up", nBins,
                            plotLow, plotHigh);
                    histo1D[("f_hdamp_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_hdamp_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_hdamp_Down", nBins,
                            plotLow, plotHigh);
                    histo1D[("f_TTJetsPDF_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] = 
                        new TH1F(("f_TTJetsPDF_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_TTJetsPDF_Up", nBins,
                            plotLow, plotHigh);
                    histo1D[("f_TTJetsPDF_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_TTJetsPDF_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_TTJetsPDF_Down", nBins,
                            plotLow, plotHigh);
                    histo1D[("f_SFjetnormcor_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_SFjetnormcor_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_SFjetnormcor_Up", nBins,
                            plotLow, plotHigh);
                    histo1D[("f_SFjetnormcor_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()] =
                        new TH1F(("f_SFjetnormcor_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str(), "f_SFjetnormcor_Down", nBins,
                            plotLow, plotHigh);
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

            if(lepiso1>0.15||lepiso2>0.15) continue;
            NormFactor = 1.0;
            SFalphaTune = 1.0;
            //SFTopPt_up = SFTopPt > 1.0? SFTopPt: 1.0;            SFTopPt_down = SFTopPt > 1.0? 1.0: SFTopPt;            SFTopPt = 1.0; 
            if(dataSetName.find("tttt") != string::npos) {
                NormFactor = 1.0 / 0.4214;
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
            } else if(dataSetName.find(mainTTbarSample) != string::npos && dataSetName.find(newTTbarSample) == string::npos && dataSetName.find("JES") == string::npos &&
                dataSetName.find("JER") == string::npos && dataSetName.find("ISR") == string::npos && dataSetName.find("FSR") == string::npos &&
                dataSetName.find("Up") == string::npos && dataSetName.find("Down") == string::npos) {

                if(genHT>=500 && n_genjets>=7 && n_genleps==2) continue;

                histo1D[("Genweight_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * GenWeight);
                histo1D[("weight1_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight1);
                histo1D[("weight2_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight2);
                histo1D[("weight3_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight3);
                histo1D[("weight4_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight4);
                histo1D[("weight5_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight5);
                histo1D[("weight6_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight6);
                histo1D[("weight7_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight7);
                histo1D[("weight8_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight8);
                histo1D[("PU_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU_up * SFTopPt * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("PU_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU_down * SFTopPt * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("TTPT_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt_up * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("TTPT_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt_down * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("btagWeightCSVLF_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFUp * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("btagWeightCSVLF_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFDown * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("btagWeightCSVHF_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFUp * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("btagWeightCSVHF_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFDown * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("btagWeightCSVHFStats1_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats1Up * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVHFStats1_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats1Down * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVHFStats2_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats2Up * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVHFStats2_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats2Down * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVLFStats1_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats1Up * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVLFStats1_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats1Down * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVLFStats2_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats2Up * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVLFStats2_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats2Down * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVCFErr1_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr1Up * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVCFErr1_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr1Down * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVCFErr2_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr2Up * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("btagWeightCSVCFErr2_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr2Down * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("heavyFlav_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight_up * cFactor * GenWeight);
                histo1D[("heavyFlav_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight_down * cFactor * GenWeight);
                histo1D[("hdamp_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * hdamp_up * GenWeight);
                histo1D[("hdamp_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * hdamp_down * GenWeight);
                histo1D[("TTJetsPDF_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * findmax(weight_ct10, weight_mmht14, (float) 1.0) * GenWeight);
                histo1D[("TTJetsPDF_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * findmin(weight_ct10, weight_mmht14, (float) 1.0) * GenWeight);
                histo1D[("SFjetnormcor_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        eqlumi * ttbbReweight * cFactor_up * GenWeight);
                histo1D[("SFjetnormcor_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        eqlumi * ttbbReweight * cFactor_down * GenWeight);

                histo1D[histoName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                        SFPU * SFTopPt * GenWeight * Luminosity * eqlumi * ttbbReweight * cFactor);

                if(split_ttbar) {
                    if(ttXrew < 1) { 
                        MSPlot[plotname]->Fill(varofInterest, ttbar_ll, true, NormFactor * GenWeight * SFtrigger * SFlepton *
                         SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * ttbbReweight * cFactor);
                    } else if(ttXrew > 1) { 
                        MSPlot[plotname]->Fill(varofInterest, ttbar_bb, true, NormFactor * GenWeight * SFtrigger * SFlepton *
                         SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * ttbbReweight * cFactor);
                    } else {
                        MSPlot[plotname]->Fill(varofInterest, ttbar_cc, true, NormFactor * GenWeight * SFtrigger * SFlepton *
                         SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * ttbbReweight * cFactor);
                    }
                } else {
                    MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * GenWeight * SFtrigger * SFlepton *
                         SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * ttbbReweight * cFactor);
                }



            } else if(dataSetName.find(newTTbarSample) != string::npos && dataSetName.find("JES") == string::npos &&
                dataSetName.find("JER") == string::npos && dataSetName.find("ISR") == string::npos && dataSetName.find("FSR") == string::npos &&
                dataSetName.find("Up") == string::npos && dataSetName.find("Down") == string::npos) {

                histo1D[("f_Genweight_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * GenWeight);
                histo1D[("f_weight1_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight1);
                histo1D[("f_weight2_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight2);
                histo1D[("f_weight3_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight3);
                histo1D[("f_weight4_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight4);
                histo1D[("f_weight5_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight5);
                histo1D[("f_weight6_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight6);
                histo1D[("f_weight7_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight7);
                histo1D[("f_weight8_tt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * weight8);
                histo1D[("f_PU_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU_up * SFTopPt * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("f_PU_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU_down * SFTopPt * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("f_TTPT_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt_up * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("f_TTPT_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt_down * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("f_btagWeightCSVLF_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFUp * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("f_btagWeightCSVLF_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFDown * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("f_btagWeightCSVHF_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFUp * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("f_btagWeightCSVHF_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFDown * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        eqlumi * ttbbReweight * cFactor * GenWeight);
                histo1D[("f_btagWeightCSVHFStats1_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats1Up * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("f_btagWeightCSVHFStats1_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats1Down * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("f_btagWeightCSVHFStats2_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats2Up * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("f_btagWeightCSVHFStats2_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats2Down * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("f_btagWeightCSVLFStats1_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats1Up * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("f_btagWeightCSVLFStats1_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats1Down * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("f_btagWeightCSVLFStats2_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats2Up * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("f_btagWeightCSVLFStats2_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats2Down * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("f_btagWeightCSVCFErr1_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr1Up * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("f_btagWeightCSVCFErr1_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr1Down * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("f_btagWeightCSVCFErr2_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr2Up * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("f_btagWeightCSVCFErr2_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr2Down * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * cFactor);
                histo1D[("f_heavyFlav_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight_up * cFactor * GenWeight);
                histo1D[("f_heavyFlav_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight_down * cFactor * GenWeight);
                histo1D[("f_hdamp_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * hdamp_up * GenWeight);
                histo1D[("f_hdamp_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * hdamp_down * GenWeight);
                histo1D[("f_TTJetsPDF_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * findmax(weight_ct10, weight_mmht14, (float) 1.0) * GenWeight);
                histo1D[("f_TTJetsPDF_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * cFactor * findmin(weight_ct10, weight_mmht14, (float) 1.0) * GenWeight);
                histo1D[("f_SFjetnormcor_Up" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        eqlumi * ttbbReweight * cFactor_up * GenWeight);
                histo1D[("f_SFjetnormcor_Down" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        eqlumi * ttbbReweight * cFactor_down * GenWeight);

                histo1D[histoName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                        SFPU * SFTopPt * GenWeight * Luminosity * eqlumi * ttbbReweight * cFactor);

                if(split_ttbar) {
                    if(ttXrew < 1) { 
                        MSPlot[plotname]->Fill(varofInterest, ttbar_ll, true, NormFactor * GenWeight * SFtrigger * SFlepton *
                         SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * ttbbReweight * cFactor * 551805.763767/6005912.2807);
                    } else if(ttXrew > 1) { 
                        MSPlot[plotname]->Fill(varofInterest, ttbar_bb, true, NormFactor * GenWeight * SFtrigger * SFlepton *
                         SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * ttbbReweight * cFactor * 551805.763767/6005912.2807);
                    } else {
                        MSPlot[plotname]->Fill(varofInterest, ttbar_cc, true, NormFactor * GenWeight * SFtrigger * SFlepton *
                         SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * ttbbReweight * cFactor * 551805.763767/6005912.2807);
                    }
                } else {
                    MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * GenWeight * SFtrigger * SFlepton *
                         SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * ttbbReweight * cFactor);
                }



            } else if(dataSetName.find("NP_overlay_ttttNLO") != string::npos && dataSetName.find("JES") == string::npos &&
                dataSetName.find("JER") == string::npos && dataSetName.find("ISR") == string::npos && dataSetName.find("FSR") == string::npos &&
                dataSetName.find("Up") == string::npos && dataSetName.find("Down") == string::npos) {

                histo1D[("Genweight_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor * GenWeight);
                histo1D[("weight1_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor * weight1);
                histo1D[("weight2_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor * weight2);
                histo1D[("weight3_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor * weight3);
                histo1D[("weight4_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor * weight4);
                histo1D[("weight5_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor * weight5);
                histo1D[("weight6_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor * weight6);
                histo1D[("weight7_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor * weight7);
                histo1D[("weight8_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor * weight8);
                histo1D[("PU_Up_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU_up * SFTopPt * Luminosity *
                        eqlumi * ttbbReweight * LumiFactor * GenWeight);
                histo1D[("PU_Down_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU_down * SFTopPt * Luminosity *
                        eqlumi * ttbbReweight * LumiFactor * GenWeight);
                histo1D[("btagWeightCSVLF_Up_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFUp * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVLF_Down_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFDown * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVHF_Up_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFUp * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVHF_Down_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFDown * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVHFStats1_Up_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats1Up * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVHFStats1_Down_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats1Down * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVHFStats2_Up_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats2Up * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVHFStats2_Down_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVHFStats2Down * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVLFStats1_Up_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats1Up * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVLFStats1_Down_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats1Down * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVLFStats2_Up_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats2Up * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVLFStats2_Down_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVLFStats2Down * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVCFErr1_Up_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr1Up * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVCFErr1_Down_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr1Down * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVCFErr2_Up_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr2Up * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);
                histo1D[("btagWeightCSVCFErr2_Down_tttt" + nameEnding).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton *
                        btagWeightCSVCFErr2Down * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        GenWeight * eqlumi * ttbbReweight * LumiFactor);

                histo1D[histoName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt *
                        GenWeight * Luminosity * eqlumi * ttbbReweight);
                MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        ttbbReweight * LumiFactor * GenWeight);
            } else if(dataSetName.find("Rare1") != string::npos) {
                histo1D[("TTJets_Rare"+plotname).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV *
                        SFalphaTune * SFPU * SFTopPt * Luminosity * GenWeight * eqlumi *
                        ttbbReweight* LumiFactor);

                histo1D[histoName.c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV *
                        SFalphaTune * SFPU * SFTopPt * GenWeight * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor);

                MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        ttbbReweight * LumiFactor * GenWeight);
            } else if( dataSetName.find("Rare2") != string::npos) {
                histo1D[("TTJets_Rare_plus"+plotname).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                        SFPU * SFTopPt * Luminosity * GenWeight * eqlumi *
                        ttbbReweight* LumiFactor);

                histo1D[histoName.c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV *
                        SFalphaTune * SFPU * SFTopPt * GenWeight * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor);

                MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        ttbbReweight * LumiFactor * GenWeight);
            } else if( dataSetName.find("EW") != string::npos || dataSetName.find("DYJets") != string::npos) {
                histo1D[("EW"+plotname).c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune *
                        SFPU * SFTopPt * Luminosity * GenWeight * eqlumi *
                        ttbbReweight* LumiFactor);

                histo1D[histoName.c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV *
                        SFalphaTune * SFPU * SFTopPt * GenWeight * Luminosity * eqlumi *
                        ttbbReweight * LumiFactor);

                MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        ttbbReweight * LumiFactor * GenWeight);
            } else if(dataSetName.find(otherTTbarsample) == string::npos && dataSetName.find("TTUE") == string::npos &&
                      dataSetName.find("JES") == string::npos && dataSetName.find("JER") == string::npos &&
                      dataSetName.find("ISR") == string::npos && dataSetName.find("FSR") == string::npos &&
                      dataSetName.find("Up") == string::npos && dataSetName.find("Down") == string::npos) {
                MSPlot[plotname]->Fill(varofInterest, datasets[d], true, NormFactor * SFtrigger * SFlepton *
                        SFbtagCSV * SFalphaTune * SFPU * SFTopPt * Luminosity *
                        ttbbReweight * LumiFactor * GenWeight);
                histo1D[histoName]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV * SFalphaTune * SFPU * SFTopPt *
                        GenWeight * Luminosity * eqlumi * ttbbReweight * LumiFactor);
            } else if(dataSetName.find("TTJets") != string::npos){
                histo1D[histoName.c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV *
                        SFalphaTune * SFPU * SFTopPt * GenWeight * Luminosity * eqlumi *
                        ttbbReweight * cFactor);
            } else {
                histo1D[histoName.c_str()]->Fill(varofInterest, NormFactor * SFtrigger * SFlepton * SFbtagCSV *
                        SFalphaTune * SFPU * SFTopPt * GenWeight * Luminosity * eqlumi *
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
                } else if(dataSetName.find("TTJetsPowheg_JESUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__JESUp";
                } else if(dataSetName.find("TTJetsPowheg_JESDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__JESDown";
                } else if(dataSetName.find("TTJetsPowheg_JERUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__JERUp";
                } else if(dataSetName.find("TTJetsPowheg_JERDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX" + "__JERDown";
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


                } else if(dataSetName.find("TTJetsPowheg_f_JESUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX_f" + "__JESUp";
                } else if(dataSetName.find("TTJetsPowheg_f_JESDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX_f" + "__JESDown";
                } else if(dataSetName.find("TTJetsPowheg_f_JERUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX_f" + "__JERUp";
                } else if(dataSetName.find("TTJetsPowheg_f_JERDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX_f" + "__JERDown";
                } else if(dataSetName.find("TTJets_f_SubTotalPileUpUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX_f" + "__SubTotalPileUpUp";
                } else if(dataSetName.find("TTJets_f_SubTotalPileUpDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX_f" + "__SubTotalPileUpDown";
                } else if(dataSetName.find("TTJets_f_SubTotalRelativeUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX_f" + "__SubTotalRelativeUp";
                } else if(dataSetName.find("TTJets_f_SubTotalRelativeDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX_f" + "__SubTotalRelativeDown";
                } else if(dataSetName.find("TTJets_f_SubTotalPtUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX_f" + "__SubTotalPtUp";
                } else if(dataSetName.find("TTJets_f_SubTotalPtDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX_f" + "__SubTotalPtDown";
                } else if(dataSetName.find("TTJets_f_SubTotalScaleUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX_f" + "__SubTotalScaleUp";
                } else if(dataSetName.find("TTJets_f_SubTotalScaleDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX_f" + "__SubTotalScaleDown";
                } else if(dataSetName.find("TTJets_f_SubTotalFlavorUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX_f" + "__SubTotalFlavorUp";
                } else if(dataSetName.find("TTJets_f_SubTotalFlavorDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "ttbarTTX_f" + "__SubTotalFlavorDown";


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

                } else if(dataSetName.find("ttttNLO_JESUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__JESUp";
                } else if(dataSetName.find("ttttNLO_JESDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__JESDown";
                } else if(dataSetName.find("ttttNLO_JERUp") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__JERUp";
                } else if(dataSetName.find("ttttNLO_JERDown") != string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + "NP_overlay_ttttNLO" + "__JERDown";
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

                } else if(dataSetName.find("TTJetsPowheg") != string::npos && dataSetName.find("TTJetsPowheg_f") == string::npos &&
                          dataSetName.find("Up") == string::npos && dataSetName.find("Down") == string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__ttbarTTX" + "__nominal";
                } else if(dataSetName.find("TTJetsPowheg_f") != string::npos &&
                          dataSetName.find("Up") == string::npos && dataSetName.find("Down") == string::npos) {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__ttbarTTX_f" + "__nominal";
                } else {
                    writename = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__" + dataSetName + "__nominal";
                }
                // cout<<"writename  :"<<writename<<endl;
                histo1D[histoName.c_str()]->Write((writename).c_str());
                //canv->SaveAs((pathPNG + histoName + ".png").c_str());
                
                

                if(dataSetName.find(mainTTbarSample) != string::npos && dataSetName.find("TTJetsPowheg_f") == string::npos &&
                    dataSetName.find("JES") == string::npos && dataSetName.find("JER") == string::npos &&
                    dataSetName.find("FSR") == string::npos && dataSetName.find("ISR") == string::npos) {
                    cout << "  making weights histos" << endl;

                    histo1D[("Genweight_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write(("Genweight_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
                    for(int ii = 1; ii < 9; ii++) {
                        string weightstring = static_cast<ostringstream*>(&(ostringstream() << ii))->str();
                        string weighthisto = "weight" + weightstring + "_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2;
                        histo1D[weighthisto]->Write(("weight" + weightstring + "_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
                    }

                    string MEScalesysname = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__ttbarTTX__";

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


                if(dataSetName.find(newTTbarSample) != string::npos &&
                    dataSetName.find("JES") == string::npos && dataSetName.find("JER") == string::npos && 
                    dataSetName.find("FSR") == string::npos && dataSetName.find("ISR") == string::npos) {
                    cout << "  making weights histos" << endl;

                    histo1D[("f_Genweight_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write(("Genweight_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
                    for(int ii = 1; ii < 9; ii++) {
                        string weightstring = static_cast<ostringstream*>(&(ostringstream() << ii))->str();
                        string weighthisto = "f_weight" + weightstring + "_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2;
                        histo1D[weighthisto]->Write(("weight" + weightstring + "_tt" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str());
                    }

                    string MEScalesysname = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__ttbarTTX_f__";

                    histo1D[("f_PU_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "PUUp").c_str());
                    histo1D[("f_PU_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "PUDown").c_str());
                    histo1D[("f_SFjetnormcor_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "SFjetnormUp").c_str());
                    histo1D[("f_SFjetnormcor_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "SFjetnormDown").c_str());
                    histo1D[("f_TTPT_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "TTPTUp").c_str());
                    histo1D[("f_TTPT_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "TTPTDown").c_str());
                    histo1D[("f_hdamp_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "TTJets_HDAMPUp").c_str());
                    histo1D[("f_hdamp_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "TTJets_HDAMPDown").c_str());
                    histo1D[("f_TTJetsPDF_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "TTJets_PDFUp").c_str());
                    histo1D[("f_TTJetsPDF_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "TTJets_PDFDown").c_str());
                    histo1D[("f_heavyFlav_Up" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "heavyFlavUp").c_str());
                    histo1D[("f_heavyFlav_Down" + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "heavyFlavDown").c_str());
                    histo1D[("f_btagWeightCSVLF_Up"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVLFUp").c_str());
                    histo1D[("f_btagWeightCSVLF_Down"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVLFDown").c_str());
                    histo1D[("f_btagWeightCSVHF_Up"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVHFUp").c_str());
                    histo1D[("f_btagWeightCSVHF_Down"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVHFDown").c_str());
                    histo1D[("f_btagWeightCSVHFStats1_Up"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats1Up").c_str());
                    histo1D[("f_btagWeightCSVHFStats1_Down"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats1Down").c_str());
                    histo1D[("f_btagWeightCSVHFStats2_Up"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats2Up").c_str());
                    histo1D[("f_btagWeightCSVHFStats2_Down"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVHFStats2Down").c_str());
                    histo1D[("f_btagWeightCSVLFStats1_Up"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats1Up").c_str());
                    histo1D[("f_btagWeightCSVLFStats1_Down"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats1Down").c_str());
                    histo1D[("f_btagWeightCSVLFStats2_Up"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats2Up").c_str());
                    histo1D[("f_btagWeightCSVLFStats2_Down"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVLFStats2Down").c_str());
                    histo1D[("f_btagWeightCSVCFErr1_Up"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr1Up").c_str());
                    histo1D[("f_btagWeightCSVCFErr1_Down"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr1Down").c_str());
                    histo1D[("f_btagWeightCSVCFErr2_Up"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr2Up").c_str());
                    histo1D[("f_btagWeightCSVCFErr2_Down"  + numStr1 + sSplitVar1 + numStr2 + sSplitVar2).c_str()]->Write((MEScalesysname + "btagWeightCSVCFErr2Down").c_str());
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
                    string MEScalesysname = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__NP_overlay_ttttNLO__";

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
    GetScaleEnvelopeSplit2_filtered(nBins, lScale, plotLow, plotHigh, leptoAbbr, shapefile, errorfile, channel, sVarofinterest,
        sSplitVar1, fbSplit1, ftSplit1, fwSplit1, sSplitVar2, fbSplit2, ftSplit2, fwSplit2, xmlNom, CraneenPath,
        shapefileName, mainTTbarSample);


//    GetErrorBandSplit2(nBins, lScale, plotLow, plotHigh, leptoAbbr, shapefile, errorfile, channel, sVarofinterest,
//        sSplitVar1, fbSplit1, ftSplit1, fwSplit1, sSplitVar2, fbSplit2, ftSplit2, fwSplit2, xmlNom, CraneenPath,
//        shapefileName, mainTTbarSample);
//    errorfile->Close();

    // treeLoader.UnLoadDataset();

    string MEScaleFileName = "ScaleFiles" + leptoAbbr + "_light/Error" + sVarofinterest + ".root";

    for(map<string, MultiSamplePlot*>::const_iterator it = MSPlot.begin(); it != MSPlot.end(); it++) {
        string name = it->first;
        MultiSamplePlot* temp = it->second;
        temp->setDataLumi(35822);

//        temp->setErrorBandFile(MEScaleFileName.c_str()); // set error file for uncertainty bands on multisample plot
        temp->Draw(sVarofinterest.c_str(), 2, false, false, false, 20);//bool addRatioErrorBand, bool addErrorBand, bool ErrorBandAroundTotalInput
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
    string newTTbarsample;
    string otherTTbarsample;
    cout << "channel  " << channel << endl;
    if(channel == "ttttmu" || channel == "ttttel") {
        mainTTbarsample = "TTJets_powheg";
        otherTTbarsample = "TTJets_MLM";
    } else {
        mainTTbarsample = "TTJetsPowheg";
        otherTTbarsample = "TTJets_MLM";
        newTTbarsample = "TTJetsPowheg_f";
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
            nChannels += 1;
        }
    }

    for(int j = 0; j < nDatasets; j++) {
        dataSetName = datasets[j]->Name();
        cout << dataSetName << endl;
        if(dataSetName.find("Data") != string::npos || dataSetName.find("data") != string::npos ||
            dataSetName.find("DATA") != string::npos || dataSetName.find("JER") != string::npos ||
            dataSetName.find("JES") != string::npos || dataSetName.find("MLM") != string::npos ||
            dataSetName.find("Up") != string::npos || dataSetName.find("Down") != string::npos ||
            dataSetName.find("TTJets_aMCatNLO")!=string::npos || dataSetName.find("Rare1TTZ") != string::npos ||
            dataSetName.find("ISR") != string::npos ||
            dataSetName.find("FSR") != string::npos || dataSetName.find("TTUE") != string::npos ||
            dataSetName.find("Rare2TTW") != string::npos || dataSetName.find("Rare2TTZ") != string::npos ||
            dataSetName.find("Rare2TTT") != string::npos || dataSetName.find("EW") != string::npos) {
            continue;
        } else {
            MCdatasets.push_back(dataSetName);
            howmanyMC += 1; 
            cout << "MC: " << dataSetName << endl;
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
            card << binname + "  ";
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
                card << binname + "  ";
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
                } else if(dataSetName.find(mainTTbarsample) != string::npos && dataSetName.find(newTTbarsample) == string::npos) {
                    card <<"ttbarTTX           ";
                } else if(dataSetName.find(newTTbarsample) != string::npos) {
                    card <<"ttbarTTX_f           ";
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
                } else if (dataSetName.find(mainTTbarsample) != string::npos && dataSetName.find(newTTbarsample) == string::npos){
                    histoName = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__ttbarTTX" + "__nominal";
                    tempHisto = (TH1F*)shapefile->Get(histoName.c_str());
                    tempEntries = tempHisto->GetSumOfWeights();
                    card << static_cast<ostringstream*>(&(ostringstream() << tempEntries))->str() + " ";

                } else if (dataSetName.find(newTTbarsample) != string::npos){
                    histoName = channel + numStr1 + sSplitVar1 + numStr2 + sSplitVar2 + "__ttbarTTX_f" + "__nominal";
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

        } else if(dataSetName.find(mainTTbarsample) != string::npos && dataSetName.find(newTTbarsample) == string::npos) {
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

        } else if(dataSetName.find(newTTbarsample) != string::npos) {
            card << "TTJets_f_norm                lnN                     ";
            for(int k = 0; k < nChannels; k++) {
                for(int dash1 = 0; dash1 < d; dash1++) {
                    card << "-                  ";
                }
                card << "0.95/1.05              ";
                for(int dash2 = howmanyMC; dash2 > d + 1; dash2--) {
                    card << "-                  ";
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

    card << "TTUE			shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                      ";
                /*    if(channel == "ttttmumu"){
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
                    }*/
            } else {
                card << "-			";
            }
        }
    }
    card << "\n";

    card << "TTISR			shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                      ";
                /*    if(channel == "ttttmumu"){ 
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
                    }*/
            } else {
                card << "-			";
            }
        }
    }
    card << "\n";

    card << "TTFSR			shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                      ";
                /*    if(channel == "ttttmumu"){ 
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
                    }*/
            } else {
                card << "-			";
            }
        }
    }
    card << "\n";

    card << "TTJets_HDAMP		shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find(mainTTbarsample) != string::npos) {
                card << "1                      ";
               /*     if(channel == "ttttmumu"){ 
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
                    }*/
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

    card << "TTTTISR			shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find("tttt") != string::npos) {
                card << "1                      ";
                /*    if(channel == "ttttmumu"){ 
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
                    }*/
            } else {
                card << "-			";
            }
        }
    }
    card << "\n";

    card << "TTTTFSR			shape			";
    for(int c = 0; c < nChannels; c++) {
        for(int d = 0; d < howmanyMC; d++) {
            dataSetName = MCdatasets[d];
            if(dataSetName.find("tttt") != string::npos) {
                card << "1                      ";
                /*    if(channel == "ttttmumu"){ 
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
                    }*/
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
