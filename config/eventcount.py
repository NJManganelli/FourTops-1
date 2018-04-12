from ROOT import TChain
from glob import glob

path = '/pnfs/iihe/cms/store/user/fblekman/TopTree/CMSSW_80X_v12/TTP-CMSSW_80X_v12--GT-80X_dataRun2_2016SeptRepro_v7/MET/crab_MET-Run2016G-03Feb2017-v1crab55/170928_173201/0000/TOPTREE_1.root'





files = glob(path)
root_files = []
for f in files:
	root_files.append('dcap://maite.iihe.ac.be' + f)
print root_files
chain = TChain('eventTree')
for rf in root_files:
	chain.Add(rf)
print 'added files'
nEntries = chain.GetEntries();
print nEntries

