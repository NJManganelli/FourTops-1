python /group/log/torque/torque-user-info.py | awk '{if(($4 != "0") && ($2 >= "23764963"))
							 print "qsub SubmitScripts/10_4_2018/Dilep/"$13";"}'
