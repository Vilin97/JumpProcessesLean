# Benchmark results

Events per second, best repetition. Julia: JumpProcesses.jl 9.33.1 on Julia 1.11.7. Lean: this repository.

| method | multistate | multisite2 | egfr_net | BCR | fceri_gamma2 |
|---|---:|---:|---:|---:|---:|
| Julia Direct | 2.19e+07 | 2.32e+06 | 1.59e+05 | 1.4e+04 | 7.06e+03 |
| Julia DirectFW | 2.11e+07 | 2.32e+06 | 1.59e+05 | 1.49e+04 | 7.92e+03 |
| Julia SortingDirect | 2.44e+07 | 6.07e+06 | 4e+06 | 1.39e+06 | 5.2e+04 |
| Julia RDirect | 1.68e+07 | 4.67e+06 | 8.69e+05 | 1.05e+05 | 5.58e+04 |
| Julia FRM | 9.83e+06 | 6.76e+05 | 5e+04 | 6.63e+03 | 2.9e+03 |
| Julia FRMFW | 1e+07 | 6.71e+05 | 5.08e+04 | 6.55e+03 | 2.92e+03 |
| Julia NRM | 1.02e+07 | 1.75e+06 | 1.41e+06 | 5.16e+05 | 2.88e+05 |
| Julia CCNRM | 9.66e+06 | 1.86e+06 | 1.92e+06 | 7.02e+05 | 4.79e+05 |
| Julia Coevolve | 8.22e+06 | 1.22e+06 | 9.9e+05 | 3.4e+05 | 1.68e+05 |
| Julia DirectCR | 1.33e+07 | 2.4e+06 | 1.9e+06 | 6.85e+05 | 4.67e+05 |
| Julia RSSA | 2.32e+07 | 6.73e+06 | 5.18e+06 | 1.98e+07 | 1.48e+04 |
| Julia RSSACR | 1.75e+07 | 1.38e+07 | 1.71e+07 | 2.07e+07 | 1.93e+06 |
| Lean Tree-RSSA G0 | 2.18e+05 | 1.25e+04 | 1.25e+03 | 175 | 71.7 |
| Lean Tree-RSSA G1 | 3.49e+06 | 2.38e+06 | 3.6e+06 | 3.47e+06 | 2.34e+05 |
| Lean Tree-RSSA G2 | 1.11e+07 | 6.33e+06 | 9.81e+06 | 1.08e+07 | 6.89e+05 |
| Lean Tree-RSSA G3 | 1.21e+07 | 7.93e+06 | 1.05e+07 | 1.15e+07 | 1.28e+06 |
| Lean Tree-RSSA G4 | 1.62e+07 | 9.71e+06 | 1.36e+07 | 1.47e+07 | 1.32e+06 |
| Lean Tree-RSSA G5 | 1.53e+07 | 9.25e+06 | 1.32e+07 | 1.36e+07 | 1.28e+06 |
| Lean Tree-RSSA G6 | 1.62e+07 | 9.55e+06 | 1.38e+07 | 1.43e+07 | 1.27e+06 |
| Lean Tree-RSSA G7 | 1.85e+07 | 1.04e+07 | 1.5e+07 | 1.69e+07 | 1.29e+06 |
| Lean Tree-RSSA G8 | 1.92e+07 | 1.06e+07 | 1.56e+07 | 1.8e+07 | 1.31e+06 |
| Lean Tree-RSSA G9 | 1.97e+07 | 1.08e+07 | 1.6e+07 | 1.85e+07 | 1.31e+06 |
| Lean Tree-RSSA G10 | 2.08e+07 | 1.11e+07 | 1.64e+07 | 1.95e+07 | 1.33e+06 |
| Lean Tree-RSSA G11 | 2.2e+07 | 1.18e+07 | 1.83e+07 | 2.34e+07 | 1.38e+06 |
| Lean Tree-RSSA G12 | 2.18e+07 | 1.22e+07 | 1.83e+07 | 2.32e+07 | 1.71e+06 |
| Lean Tree-RSSA G13 | 2.21e+07 | 1.27e+07 | 1.87e+07 | 2.34e+07 | 1.77e+06 |
| Lean Tree-RSSA G14 | 2.23e+07 | 1.26e+07 | 1.87e+07 | 2.38e+07 | 1.77e+06 |
| Lean Tree-RSSA G15 | 2.53e+07 | 1.35e+07 | 1.98e+07 | 2.72e+07 | 1.78e+06 |
| Lean Tree-RSSA G16 | 2.51e+07 | 1.46e+07 | 2.04e+07 | 2.68e+07 | 2.3e+06 |
| Lean Tree-RSSA G17 | 2.94e+07 | 1.59e+07 | 2.21e+07 | 3.25e+07 | 2.3e+06 |
| Lean Tree-RSSA G18 | 3.09e+07 | 1.74e+07 | 2.29e+07 | 3.32e+07 | 2.62e+06 |
| Lean Tree-RSSA G19 | 3.3e+07 | 1.84e+07 | 2.33e+07 | 3.3e+07 | 2.84e+06 |
| Lean Tree-RSSA G20 | 3.59e+07 | 1.97e+07 | 2.42e+07 | 3.49e+07 | 3.11e+06 |
| Lean Tree-RSSA G21 | 3.62e+07 | 2.04e+07 | 2.46e+07 | 3.6e+07 | 3.2e+06 |
| Lean Tree-RSSA G22 | 3.74e+07 | 2.04e+07 | 2.55e+07 | 3.89e+07 | 3.39e+06 |
| Lean Tree-RSSA G23 | 3.73e+07 | 2e+07 | 2.55e+07 | 3.94e+07 | 3.4e+06 |
| Lean Tree-RSSA G24 | 3.73e+07 | 2.01e+07 | 2.62e+07 | 3.92e+07 | 3.43e+06 |
| Lean Tree-RSSA G25 | 3.77e+07 | 2.03e+07 | 2.69e+07 | 4.06e+07 | 3.42e+06 |
| Lean Tree-RSSA G26 | 3.76e+07 | 2.01e+07 | 2.66e+07 | 4.07e+07 | 3.42e+06 |
| Lean Tree-RSSA G27 | 3.76e+07 | 2.01e+07 | 2.68e+07 | 4.07e+07 | 3.47e+06 |
| Lean Tree-RSSA G28 | 3.75e+07 | 2.03e+07 | 2.66e+07 | 4.07e+07 | 3.5e+06 |
| Tree-RSSA in C (unverified cross-check) | 3.04e+07 | 1.43e+07 | 2.17e+07 | 3.51e+07 | 1.56e+06 |
| Lean RSSACR port | 6.22e+06 | 4.6e+06 | 6.41e+06 | 7.58e+06 | 6.6e+05 |
| Lean FloatLib Direct | 2.07e+04 | 1.6e+03 | 179 | 29.4 | 10.4 |
| Lean FloatLib NRM | 9.51e+03 | 557 | 115 | 17.3 | 6.14 |
| Lean FloatLib RSSA | 8.12e+03 | 599 | 46.6 | 6.37 | 2.51 |

## Head to head (same window, alternating rounds, best time)

| network | fastest Julia | Julia ev/s | Lean G28 ev/s | ratio | C ev/s |
|---|---|---:|---:|---:|---:|
| multistate | SortingDirect | 2.45e+07 | 3.77e+07 | 1.53 | 3.05e+07 |
| multisite2 | RSSACR | 1.39e+07 | 2.03e+07 | 1.45 | 1.43e+07 |
| egfr_net | RSSACR | 1.7e+07 | 2.66e+07 | 1.56 | 2.17e+07 |
| BCR | RSSACR | 2.51e+07 | 4.09e+07 | 1.63 | 3.52e+07 |
| fcεRI γ2 | RSSACR | 1.88e+06 | 3.48e+06 | 1.85 | 1.55e+06 |

Machine: {"julia": {"cpu": "AMD Ryzen 9 9955HX 16-Core Processor", "platform": "Linux-7.0.0-38-generic-x86_64-with-glibc2.43", "commit": "5a0609aa9769f170dfe97826e357109e3eb3555a", "dirty": true, "date": "2026-10-12T07:48:37+00:00"}, "lean": {"cpu": "AMD Ryzen 9 9955HX 16-Core Processor", "platform": "Linux-7.0.0-38-generic-x86_64-with-glibc2.43", "commit": "409e4b9374fdd38a22728b0f77b2575edead5ae8", "dirty": true, "date": "2026-10-10T13:09:45+00:00"}, "generations": {"cpu": "AMD Ryzen 9 9955HX 16-Core Processor", "platform": "Linux-7.0.0-38-generic-x86_64-with-glibc2.43", "commit": "ab9683ddd6d043f9f507142bee98d733c11a2eff", "dirty": false, "date": "2026-10-17T10:04:28+00:00"}}
