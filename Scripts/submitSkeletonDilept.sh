#!/bin/bash
#PBS -q localgrid
#PBS -l walltime=4:00:00
# setting up your code and your env
source /user/lowang/.bash_profile
cd /user/lowang/CMSSW_8_0_26_patch1/src
eval `scramv1 runtime -sh`
cd TopBrussels/FourTops

# want you really want to do!!

