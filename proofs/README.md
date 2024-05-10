# TLAPS Proof Checking

You can install the TLA+ proof system (TLAPS) by following the instructions [here](https://tla.msr-inria.inria.fr/tlaps/content/Download/Binaries.html).

Note: the links to the binaries on the inria site are broken. There's already a GitHub issue filed about the broken links.
* Broken: `https://github.com/tlaplus/tlapm/releases/download/202210041448/tlaps-1.4.5-x86_64-linux-gnu-inst.bin`
* Fixed: `https://github.com/tlaplus/tlapm/releases/tag/v1.4.5`

You can check the TLAPS proofs in a file from the command line as follows (e.g., for the `consensus_epr` spec):
```bash
python3 checkproofs.py --tla_file consensus_epr_IndProofs.tla
```
Upon successful checking of all proof obligations in that file, you should see a message output like the following:
```
Checking proofs from 1 files
Checking proof in 'consensus_epr_IndProofs.tla' with tlapm (1/1)
tlapm cmd: tlapm  --stretch 1 --threads 6 --toolbox 0 0 -I /usr/local/lib/tlaps/ --cleanfp --nofp consensus_epr_IndProofs.tla
tlapm checked proof in 6.01s
Parsed proof results for 'consensus_epr_IndProofs.tla'
Saved HTML proof report to 'consensus_epr_IndProofs.tla.proofs.html'.
Proof obligation results: 223/223 obligations proved.
Success: all obligations proven!
Checked all proofs successfully!
```
Note that you can also check TLAPS proofs interactively using the TLA+ Toolbox, whose instructions for installation can be found [here](https://lamport.azurewebsites.net/tla/toolbox.html).

## Current Status

<!-- Table with row for each protocol and column with "checked" -->
<!-- unicode check mark -->

Config indices refer to the ID column in Table I of the paper. The solution that
was verified with TLAPS may have been synthesized for multiple config indices;
we list all of them.

| Protocol | TLAPS Proof Checked | Config Indices |
|----------|---------|---------|
| `consensus_epr` | ✓ | 624 |
| `consensus_epr2` | ✓ | 550 |
| `lock_serv` | ✓ | 599,611 |
| `mldr_sm` | ✓ | 121,343 |
| `mldr_sm3` | ✓ | 463 |
| `peterson` | ✓ (finite) | 413, 475 |
| `peterson2` | ✓ (finite) | 375 |
| `peterson3` | ✓ (finite) | 547 |
| `sharded_kv` | ✓ | 302 |
| `sharded_kv2` | ✓ | 365 |
| `simple_decentralized_lock` | ✓ | 486 |
| `two_phase_commit` | ✓ | 513 |
| `two_phase_commit2` | ✓ | 303, 485 |
| `two_phase_commit3` | ✓ | 558 |
| `mldr` | ✓ | 710,709 |
| `mldr3` | ✓ | 708,714 |

