# Frap2018

Here are a few solutions I wrote for the problem sets in
https://github.com/mit-frap/spring18,
MIT 6.822 Formal Reasoning About Programs (Spring 2018).

Note that I skipped Pset8 and Pset11.

### Note on Coq version and compiling

This repo and its solutions assume you are using Coq 8.11.0.

Since the frap submodule was linked from an earlier version that did not compile
under Coq 8.11.0, make sure to run the script `update_frap.sh` before trying to
compile the library.

```
$ source configure_coqbin.sh # optional
$ git submodule init
$ git submodule update
$ ./update_frap.sh  # NEW STEP for Coq 8.11.0
$ make -C frap lib
$ make -C pset1
```

