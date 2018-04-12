#! /bin/bash

ls ./SubmitScripts/10_4_2018/Dilep/submit_*.sh | awk '{print "qsub -q localgrid "$1"\n"}' | sh
