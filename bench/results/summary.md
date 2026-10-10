# Benchmark results

Events per second, best repetition. Julia: JumpProcesses.jl 9.33.1 on Julia 1.11.7. Lean: this repository.

| method | multistate | multisite2 | egfr_net | BCR | fceri_gamma2 |
|---|---:|---:|---:|---:|---:|
| Julia Direct | 2.19e+07 | 2.32e+06 | 1.59e+05 | 1.4e+04 | 7.06e+03 |
| Julia SortingDirect | 2.44e+07 | 6.07e+06 | 4e+06 | 1.39e+06 | 5.2e+04 |
| Julia RDirect | 1.68e+07 | 4.67e+06 | 8.69e+05 | 1.05e+05 | 5.58e+04 |
| Julia FRM | 9.83e+06 | 6.76e+05 | 5e+04 | 6.63e+03 | 2.9e+03 |
| Julia NRM | 1.02e+07 | 1.75e+06 | 1.41e+06 | 5.16e+05 | 2.88e+05 |
| Julia CCNRM | 9.66e+06 | 1.86e+06 | 1.92e+06 | 7.02e+05 | 4.79e+05 |
| Julia DirectCR | 1.33e+07 | 2.4e+06 | 1.9e+06 | 6.85e+05 | 4.67e+05 |
| Julia RSSA | 2.32e+07 | 6.73e+06 | 5.18e+06 | 1.98e+07 | 1.48e+04 |
| Julia RSSACR | 1.75e+07 | 1.38e+07 | 1.71e+07 | 2.07e+07 | 1.93e+06 |
| Lean Tree-RSSA G0 | 2.18e+05 | 1.25e+04 | 1.25e+03 | 175 | 71.7 |
| Lean Tree-RSSA G1 | 3.49e+06 | 2.38e+06 | 3.6e+06 | 3.47e+06 | 2.34e+05 |
| Lean Tree-RSSA G2 | 1.13e+07 | 6.34e+06 | 1.01e+07 | 1.08e+07 | 6.84e+05 |
| Lean Tree-RSSA G3 | 1.24e+07 | 8.13e+06 | 1.08e+07 | 1.15e+07 | 1.27e+06 |
| Lean Tree-RSSA G4 | 1.67e+07 | 1e+07 | 1.42e+07 | 1.49e+07 | 1.3e+06 |
| Lean Tree-RSSA G5 | 1.53e+07 | 9.39e+06 | 1.35e+07 | 1.36e+07 | 1.26e+06 |
| Lean Tree-RSSA G6 | 1.66e+07 | 9.8e+06 | 1.43e+07 | 1.43e+07 | 1.25e+06 |
| Lean Tree-RSSA G7 | 1.91e+07 | 1.07e+07 | 1.58e+07 | 1.68e+07 | 1.27e+06 |
| Lean Tree-RSSA G8 | 1.97e+07 | 1.09e+07 | 1.62e+07 | 1.8e+07 | 1.3e+06 |
| Lean Tree-RSSA G9 | 2.03e+07 | 1.1e+07 | 1.66e+07 | 1.86e+07 | 1.3e+06 |
| Lean Tree-RSSA G10 | 2.13e+07 | 1.14e+07 | 1.72e+07 | 1.95e+07 | 1.31e+06 |
| Lean Tree-RSSA G11 | 2.23e+07 | 1.2e+07 | 1.93e+07 | 2.32e+07 | 1.35e+06 |
| Lean Tree-RSSA G12 | 2.23e+07 | 1.27e+07 | 1.95e+07 | 2.29e+07 | 1.67e+06 |
| Lean Tree-RSSA G13 | 2.26e+07 | 1.32e+07 | 1.99e+07 | 2.32e+07 | 1.8e+06 |
| Lean Tree-RSSA G14 | 2.37e+07 | 1.34e+07 | 2.04e+07 | 2.4e+07 | 1.8e+06 |
| Lean Tree-RSSA G15 | 2.65e+07 | 1.43e+07 | 2.18e+07 | 2.7e+07 | 1.8e+06 |
| Lean Tree-RSSA G16 | 2.65e+07 | 1.56e+07 | 2.2e+07 | 2.71e+07 | 2.33e+06 |
| Tree-RSSA in C (unverified cross-check) | 3.4e+07 | 1.59e+07 | 2.64e+07 | 3.63e+07 | 1.62e+06 |
| Lean RSSACR port | 6.5e+06 | 4.82e+06 | 6.89e+06 | 7.84e+06 | 6.55e+05 |
| Lean FloatLib Direct | 2.07e+04 | 1.6e+03 | 179 | 29.4 | 10.4 |
| Lean FloatLib NRM | 9.51e+03 | 557 | 115 | 17.3 | 6.14 |
| Lean FloatLib RSSA | 8.12e+03 | 599 | 46.6 | 6.37 | 2.51 |

## Head to head (same window, alternating rounds, best time)

| network | fastest Julia | Julia ev/s | Lean G16 ev/s | ratio | C ev/s |
|---|---|---:|---:|---:|---:|
| multistate | SortingDirect | 2.45e+07 | 2.65e+07 | 1.08 | 3.38e+07 |
| multisite2 | RSSACR | 1.42e+07 | 1.55e+07 | 1.09 | 1.59e+07 |
| egfr_net | RSSACR | 1.7e+07 | 2.21e+07 | 1.30 | 2.52e+07 |
| BCR | RSSACR | 2.48e+07 | 2.7e+07 | 1.09 | 3.64e+07 |
| fcεRI γ2 | RSSACR | 1.88e+06 | 2.34e+06 | 1.25 | 1.63e+06 |

Machine: {"julia": {"cpu": "AMD Ryzen 9 9955HX 16-Core Processor", "platform": "Linux-7.0.0-38-generic-x86_64-with-glibc2.43", "commit": "0c864b0859447f66a1403ac9c086d9d81568b63b", "date": "2026-10-08T16:22:17+00:00"}, "lean": {"cpu": "AMD Ryzen 9 9955HX 16-Core Processor", "platform": "Linux-7.0.0-38-generic-x86_64-with-glibc2.43", "commit": "409e4b9374fdd38a22728b0f77b2575edead5ae8", "dirty": true, "date": "2026-10-10T13:09:45+00:00"}, "generations": {"cpu": "AMD Ryzen 9 9955HX 16-Core Processor", "platform": "Linux-7.0.0-38-generic-x86_64-with-glibc2.43", "commit": "409e4b9374fdd38a22728b0f77b2575edead5ae8", "dirty": true, "date": "2026-10-10T12:15:05+00:00"}}
