# LogRobin++

This repository implements the Robin++/LogRobin/LogRobin++ protocol.
See our paper for details.

Basis
=====
Our LogRobin++ is based on (1) QuickSilver's (https://eprint.iacr.org/2021/076) repository, which is part of the EMP Toolkit: https://github.com/emp-toolkit/emp-zk; and (2) Batchman's (https://github.com/gconeice/stacking-vole-zk) repository. In particular, we forked their repositories and developed based on them. We also tweak some of EMP's libraries.

MIT license is included as part of each repository.

Prerequisites
=====
This repo requires the following prerequisites (on Ubuntu):
`git software-properties-common cmake build-essential libssl-dev clang`

They can be installed using `apt-get` in a standard way:
`sudo apt-get install -y software-properties-common cmake build-essential libssl-dev clang`

We recommend to install `iperf` to test for the simulated network as well.

Setup environment
=====
This includes installation of [emp-tool](https://github.com/emp-toolkit/emp-tool) and [emp-ot](https://github.com/emp-toolkit/emp-ot).

We provide the following script to install them under the folder `setup`:
`bash setup.sh`

Build and install
=====
We provide the following script to install them under the folder `build`:
`bash install.sh`

Toy example
=====
Let `$IP` denote the prover's IP address.

Prover:
`./build/bin/test_rep_bool_logrobinplus_ro 1 12345 localhost 1 10 10000000`

Verifier:
`./build/bin/test_rep_bool_logrobinplus_ro 2 12345 $IP 1 10 10000000`

Browsing the code
=====
`/test/rand` contains our core code for branches with different circuits.

`/test/rep` contains our core code for branches with a same circuit.

`/emp-zk` contains the EMP Toolkit's ZK library.

Expected executable
=====
After compiling, the executable would show up in `build/bin`.

Test
=====
See the Excel file `benchmark_summary.xlsx`, which includes the data to generate the tables and plots in our paper.

See the file `ae_appendix.pdf`, which includes how to obtain the numbers in the Excel and paper step-by-step.