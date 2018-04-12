#!/bin/bash
#PBS -q localgrid
#PBS -l walltime=3:00:00
# setting up your code and your env
source /user/lbeck/.bash_profile
cd /user/lbeck/CMSSW_7_6_3/src/TopBrussels/FourTops
eval `scramv1 runtime -sh`

# want you really want to do!!

