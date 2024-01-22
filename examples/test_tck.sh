TIME_LIMIT=7200 # 2 hours
MEM_LIMIT=8000000 # 8GB
ulimit -t ${TIME_LIMIT} -v ${MEM_LIMIT}
set -x
time tck-liveness -a couvscc ums-1/product-ltl1.tck -l live
time tck-liveness -a couvscc ums-1/product-ltl2.tck -l live
time tck-liveness -a couvscc ums-2/product-ltl1.tck -l live
time tck-liveness -a couvscc ums-2/product-ltl2.tck -l live
time tck-liveness -a couvscc sdn/product-ltl1.tck -l live
time tck-liveness -a couvscc sdn/product-ltl2.tck -l live
time tck-reach -a reach sdn/product-ltl1.tck -l err
time tck-reach -a reach ums-1/product-ltl1.tck -l err
time tck-reach -a reach ums-2/product-ltl1.tck -l err
