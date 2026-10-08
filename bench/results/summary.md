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
| Lean Tree-RSSA G0 | 1.82e+05 | 8.83e+03 | 1.06e+03 | 130 | 43.4 |
| Lean Tree-RSSA G1 | 3.48e+06 | 2.19e+06 | 3.07e+06 | 2.84e+06 | 1.77e+05 |
| Lean Tree-RSSA G2 | 8.78e+06 | 5.02e+06 | 9.4e+06 | 7.52e+06 | 5.73e+05 |
| Lean Tree-RSSA G3 | 9.67e+06 | 6.42e+06 | 8.71e+06 | 8.53e+06 | 1.22e+06 |
| Lean Tree-RSSA G4 | 1.26e+07 | 7.48e+06 | 1.12e+07 | 1.06e+07 | 1.07e+06 |
| Lean Tree-RSSA G5 | 1.31e+07 | 6.58e+06 | 1.07e+07 | 1.07e+07 | 1.06e+06 |
| Lean Tree-RSSA G6 | 1.22e+07 | 7.17e+06 | 1.15e+07 | 1.15e+07 | 1.04e+06 |
| Lean Tree-RSSA G7 | 1.47e+07 | 8.02e+06 | 1.26e+07 | 1.32e+07 | 1.18e+06 |
| Lean Tree-RSSA G8 | 1.56e+07 | 7.93e+06 | 1.3e+07 | 1.48e+07 | 1.25e+06 |
| Lean Tree-RSSA G9 | 1.6e+07 | 8.8e+06 | 1.56e+07 | 1.45e+07 | 1.28e+06 |
| Lean Tree-RSSA G10 | 1.62e+07 | 1.08e+07 | 1.3e+07 | 1.57e+07 | 1.3e+06 |
| Tree-RSSA in C (unverified cross-check) | 2.44e+07 | 1.3e+07 | 1.88e+07 | 2.79e+07 | 1.58e+06 |
| Lean RSSACR port | 5.63e+06 | 4.47e+06 | 5.96e+06 | 7.58e+06 | 6.55e+05 |
| Lean FloatLib Direct | 2.07e+04 | 1.6e+03 | 179 | 29.4 | 10.4 |
| Lean FloatLib NRM | 9.51e+03 | 557 | 115 | 17.3 | 6.14 |
| Lean FloatLib RSSA | 8.12e+03 | 599 | 46.6 | 6.37 | 2.51 |

## Head to head (same window, alternating rounds, best time)

| network | fastest Julia | Julia ev/s | Lean G10 ev/s | ratio | C ev/s | Lean RSSACR port ev/s |
|---|---|---:|---:|---:|---:|---:|
| multistate | SortingDirect | 2.11e+07 | 1.92e+07 | 0.91 | 2.92e+07 | 6.77e+06 |
| multisite2 | RSSACR | 1.4e+07 | 1.08e+07 | 0.77 | 1.5e+07 | 4.92e+06 |
| egfr_net | RSSACR | 1.69e+07 | 1.62e+07 | 0.96 | 2.39e+07 | 7.09e+06 |
| BCR | RSSACR | 2.37e+07 | 1.8e+07 | 0.76 | 3.3e+07 | 9.16e+06 |
| fcεRI γ2 | RSSACR | 1.77e+06 | 1.1e+06 | 0.62 | 1.42e+06 | 6.15e+05 |

Machine: {"julia": {"cpu": "AMD Ryzen 9 9955HX 16-Core Processor", "platform": "Linux-7.0.0-38-generic-x86_64-with-glibc2.43", "commit": "0c864b0859447f66a1403ac9c086d9d81568b63b", "date": "2026-10-08T16:22:17+00:00"}, "lean": {"cpu": "AMD Ryzen 9 9955HX 16-Core Processor", "platform": "Linux-7.0.0-38-generic-x86_64-with-glibc2.43", "commit": "1a4956498c60d66955fa9b2976d4d48cc82dd95a", "date": "2026-10-08T18:16:39+00:00"}, "generations": {"cpu": "AMD Ryzen 9 9955HX 16-Core Processor", "platform": "Linux-7.0.0-38-generic-x86_64-with-glibc2.43", "commit": "ece8fde274b65ff130f42358ae4b7327dc99c0db", "date": "2026-10-08T20:10:51+00:00"}}
