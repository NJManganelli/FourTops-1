qstat localgrid@cream02 |grep lowang |awk '{print "qdel "$1}'|xargs -0 bash -c
