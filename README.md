# LogRobin++

This repository implements the Robin++/LogRobin/LogRobin++ protocol.
See our paper for details.

Basis on EMP
=====
Our LogRobin++ is based on (1) QuickSilver's (https://eprint.iacr.org/2021/076) repository, which is part of the EMP Toolkit: https://github.com/emp-toolkit/emp-zk; and (2) Batchman's (https://github.com/gconeice/stacking-vole-zk) repository. In particular, we forked their repositories and developed based on them. We also tweak some of EMP's libraries.
In our final open source version, we will further clarify all changes.

MIT license is included as part of each repository.

Setup environment
=====
`sudo bash setup.sh`

Build and install
=====
`bash install.sh`

Browsing the code
=====
`/test/logrobinplus` contains our core code for branches with different circuits.

`/test/rep` contains our core code for branches with a same circuit.

`/emp-zk` contains the EMP Toolkit's ZK library.

Expected executable
=====
After compiling, the executable would show up in `build/bin`.

Test
=====
We will further explain how one can reproduce all results in the paper when we de-anonymize the repository.