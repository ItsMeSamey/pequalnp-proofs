import resource,subprocess,time
start=time.monotonic()
for cmd in (['g++','-Os','--param=ggc-min-expand=5','--param=ggc-min-heapsize=1024','-fno-inline','-std=c++20','orcut18272_four.cpp','-o','orcut18272_four'],['./orcut18272_four','0','0','1']):
    u=resource.getrusage(resource.RUSAGE_CHILDREN)
    rem=int(6-u.ru_utime-u.ru_stime)
    if rem<1:break
    def limit():
        resource.setrlimit(resource.RLIMIT_CPU,(rem,rem))
        resource.setrlimit(resource.RLIMIT_AS,(145<<20,145<<20))
    print('launch',cmd[0],rem,flush=True)
    try: ret=subprocess.run(cmd,timeout=max(.1,15-(time.monotonic()-start)),preexec_fn=limit).returncode
    except subprocess.TimeoutExpired:ret=124
    print('return',ret,flush=True)
    if ret:break
u=resource.getrusage(resource.RUSAGE_CHILDREN)
print('CPU',u.ru_utime+u.ru_stime,'RSSKiB',u.ru_maxrss,'wall',time.monotonic()-start)
