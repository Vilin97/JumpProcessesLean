// An independent, unverified C implementation of Tree-RSSA with the same arithmetic as the
// Lean specification: heap sum tree, population brackets, xoshiro256++ seeded through
// SplitMix64, exponentials by the 256-layer ziggurat of JumpProcessesLean/HostFloat.lean. It serves two purposes in the benchmark:
//   * a cross-check: its final populations must equal those of every Lean generation for the
//     same seed (bench/generations.py compares the digests);
//   * a calibration of the Lean code against straightforward C.
// build: cc -O3 -march=native -ffp-contract=off -o treerssa bench/c/treerssa.c -lm
// usage: treerssa <model.rn> <T> [seed]
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef struct { int nr; int *rs; int *rn; int nc; int *cs; long *cd; double rate; } Rx;

static uint64_t s0, s1, s2, s3;
static inline uint64_t rotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static inline uint64_t next(void) {
  uint64_t result = rotl(s0 + s3, 23) + s0, t = s1 << 17;
  s2 ^= s0; s3 ^= s1; s1 ^= s2; s0 ^= s3; s2 ^= t; s3 = rotl(s3, 45);
  return result;
}
static uint64_t splitmix(uint64_t *x) {
  uint64_t z = (*x += 0x9e3779b97f4a7c15ULL);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  return z ^ (z >> 31);
}
static const double P53 = 1.1102230246251565e-16, P52 = 2.220446049250313e-16;

// Ziggurat layer widths X[0..256] and densities F[i] = exp(-X[i]), as exact bit patterns.
static const uint64_t ZX[257] = {
  0x402164ec94bf5dc1ULL, 0x401ec9d9297ebb83ULL, 0x401bc39e51da71fcULL, 0x4019e9dc0d487b85ULL,
  0x4018939fe6f2ed19ULL, 0x40178750d6eac62fULL, 0x4016aa676d4bbf72ULL, 0x4015ee7ae17313d2ULL,
  0x40154ad83ccf73f6ULL, 0x4014b9d7cd4751d1ULL, 0x4014379766e41362ULL, 0x4013c14ec7c8b861ULL,
  0x401354ee27ccf75eULL, 0x4012f0e38a4411f0ULL, 0x401293f5ae49aaa5ULL, 0x40123d2bb659919fULL,
  0x4011ebbca0c9fa7cULL, 0x40119f03bcb3c2d6ULL, 0x401156786775442aULL, 0x401111a8034392a6ULL,
  0x4010d031785d48a0ULL, 0x401091c1cdcba54eULL, 0x401056118bf58eefULL, 0x40101ce2b362ec2eULL,
  0x400fcbfe43f6c6e5ULL, 0x400f626e9791f7a7ULL, 0x400efcc26750ea4aULL, 0x400e9aaf2af383c1ULL,
  0x400e3bf26e190960ULL, 0x400de050af4ef19fULL, 0x400d87946fec3becULL, 0x400d318d6b2738c5ULL,
  0x400cde0fecf2a97fULL, 0x400c8cf442c8c8f4ULL, 0x400c3e1641c2e0a7ULL, 0x400bf154de4bef77ULL,
  0x400ba691d276da5eULL, 0x400b5db15091ea0fULL, 0x400b1699c003b60aULL, 0x400ad13382d845c4ULL,
  0x400a8d68c2ad86eaULL, 0x400a4b2543e84c3bULL, 0x400a0a563e49f178ULL, 0x4009caea3a24d9eaULL,
  0x40098cd0f18d1ad8ULL, 0x40094ffb34fc2a0eULL, 0x4009145ad2f37544ULL, 0x4008d9e2823b3695ULL,
  0x4008a085ce695babULL, 0x4008683906687342ULL, 0x400830f12cc0bec3ULL, 0x4007faa3e96e1412ULL,
  0x4007c5477d1476d3ULL, 0x400790d2b56b71f9ULL, 0x40075d3ce2bd71c3ULL, 0x40072a7dce5cd218ULL,
  0x4006f88db1f42507ULL, 0x4006c7652f9a7b1eULL, 0x400696fd4a9748eeULL, 0x4006674f60c3f432ULL,
  0x40063855247b2e94ULL, 0x40060a0897081879ULL, 0x4005dc640388bd9eULL, 0x4005af61fa38e107ULL,
  0x400582fd4c1b4461ULL, 0x4005573106f8a75aULL, 0x40052bf871acaab2ULL, 0x4005014f08b99508ULL,
  0x4004d7307b1cb127ULL, 0x4004ad98a75da14cULL, 0x4004848398d39432ULL, 0x40045bed851bc92cULL,
  0x400433d2c9bd42f8ULL, 0x40040c2fe9f5eeadULL, 0x4003e5018cadded0ULL, 0x4003be447a8d8b83ULL,
  0x400397f59c345143ULL, 0x40037211f88ca856ULL, 0x40034c96b33bc965ULL, 0x400327810b2aa7d0ULL,
  0x400302ce59265965ULL, 0x4002de7c0e962d70ULL, 0x4002ba87b445db51ULL, 0x400296eee942532bULL,
  0x400273af61c7daa6ULL, 0x400250c6e6403bbaULL, 0x40022e33524fe550ULL, 0x40020bf293f0f4a2ULL,
  0x4001ea02aa9b3370ULL, 0x4001c861a6782a5aULL, 0x4001a70da7a27820ULL, 0x40018604dd6fae9eULL,
  0x4001654585c404c1ULL, 0x400144cdec6f3a2bULL, 0x4001249c6a92154aULL, 0x400104af660befceULL,
  0x4000e50550efcfb7ULL, 0x4000c59ca900946fULL, 0x4000a673f733c819ULL, 0x40008789cf3aad0fULL,
  0x400068dccf1126dbULL, 0x40004a6b9e9224a3ULL, 0x40002c34ef11391bULL, 0x40000e377af911d4ULL,
  0x3fffe0e40add09d8ULL, 0x3fffa5c6b3efe1e5ULL, 0x3fff6b1498515ed0ULL, 0x3fff30cb6ea0bc7fULL,
  0x3ffef6e8fc5b9168ULL, 0x3ffebd6b154a7678ULL, 0x3ffe844f9af4237fULL, 0x3ffe4b947c16a452ULL,
  0x3ffe1337b426509cULL, 0x3ffddb374ad2357fULL, 0x3ffda391538da50aULL, 0x3ffd6c43ed1ea3ffULL,
  0x3ffd354d4130f2adULL, 0x3ffcfeab83ed7180ULL, 0x3ffcc85cf395a56cULL, 0x3ffc925fd82323fbULL,
  0x3ffc5cb282eab1a4ULL, 0x3ffc27534e42e02dULL, 0x3ffbf2409d2dfd85ULL, 0x3ffbbd78db072610ULL,
  0x3ffb88fa7b324fb6ULL, 0x3ffb54c3f8cf2542ULL, 0x3ffb20d3d66e8bb5ULL, 0x3ffaed289dcaacffULL,
  0x3ffab9c0df81657aULL, 0x3ffa869b32d0f30fULL, 0x3ffa53b63556c690ULL, 0x3ffa21108ad0592dULL,
  0x3ff9eea8dcdde951ULL, 0x3ff9bc7ddac7035dULL, 0x3ff98a8e3940bbf4ULL, 0x3ff958d8b235828aULL,
  0x3ff9275c048e73e1ULL, 0x3ff8f616f3fe1513ULL, 0x3ff8c50848cc6094ULL, 0x3ff8942ecfa40f54ULL,
  0x3ff86389596108e7ULL, 0x3ff83316badfe62aULL, 0x3ff802d5ccce7277ULL, 0x3ff7d2c56b7d17f7ULL,
  0x3ff7a2e476b1240aULL, 0x3ff77331d177d130ULL, 0x3ff743ac61fa041cULL, 0x3ff714531150a9fbULL,
  0x3ff6e524cb59a608ULL, 0x3ff6b6207e8d3cdfULL, 0x3ff687451bd3ebeeULL, 0x3ff65891965c9b8cULL,
  0x3ff62a04e3731a2eULL, 0x3ff5fb9dfa56cf26ULL, 0x3ff5cd5bd4119335ULL, 0x3ff59f3d6b4e9cf9ULL,
  0x3ff57141bc316f27ULL, 0x3ff54367c42cb5f8ULL, 0x3ff515ae81d900fbULL, 0x3ff4e814f4cb45eaULL,
  0x3ff4ba9a1d6b18a4ULL, 0x3ff48d3cfcc883c4ULL, 0x3ff45ffc94716ca7ULL, 0x3ff432d7e6466cd0ULL,
  0x3ff405cdf44f09c4ULL, 0x3ff3d8ddc08d336dULL, 0x3ff3ac064ccfeffcULL, 0x3ff37f469a851af0ULL,
  0x3ff3529daa8a1ba1ULL, 0x3ff3260a7cfb7611ULL, 0x3ff2f98c11031721ULL, 0x3ff2cd2164a53b5dULL,
  0x3ff2a0c9748bcdaaULL, 0x3ff274833bd0189fULL, 0x3ff2484db3c2a329ULL, 0x3ff21c27d3b10e05ULL,
  0x3ff1f01090a9c4e2ULL, 0x3ff1c406dd3d5283ULL, 0x3ff19809a93d2396ULL, 0x3ff16c17e1777ffbULL,
  0x3ff140306f707dbeULL, 0x3ff114523917ac15ULL, 0x3ff0e87c207a2f66ULL, 0x3ff0bcad03710137ULL,
  0x3ff090e3bb4b0072ULL, 0x3ff0651f1c7276f8ULL, 0x3ff0395df60db162ULL, 0x3ff00d9f119a3cd9ULL,
  0x3fefc3c26504a9a1ULL, 0x3fef6c462b57feb5ULL, 0x3fef14c6e20294a0ULL, 0x3feebd41e5e21b62ULL,
  0x3fee65b483cf1044ULL, 0x3fee0e1bf77c31feULL, 0x3fedb6756a429057ULL, 0x3fed5ebdf1d86b8dULL,
  0x3fed06f28ef0e6fbULL, 0x3fecaf102bc25adbULL, 0x3fec57139a70d29fULL, 0x3febfef99359fe99ULL,
  0x3feba6beb33f8f89ULL, 0x3feb4e5f794c979bULL, 0x3feaf5d844f224c9ULL, 0x3fea9d255396d261ULL,
  0x3fea4442be14884aULL, 0x3fe9eb2c75ff03bfULL, 0x3fe991de42ad1338ULL, 0x3fe93853bdfda244ULL,
  0x3fe8de8850d0c52aULL, 0x3fe884772f2be1ecULL, 0x3fe82a1b53fed599ULL, 0x3fe7cf6f7c7e8172ULL,
  0x3fe7746e23077973ULL, 0x3fe71911797990bbULL, 0x3fe6bd5362faa944ULL, 0x3fe6612d6d0c68e0ULL,
  0x3fe60498c7dd2ecfULL, 0x3fe5a78e3db8befdULL, 0x3fe54a0629786f4dULL, 0x3fe4ebf86bcd0b93ULL,
  0x3fe48d5c5f35e712ULL, 0x3fe42e28ca706748ULL, 0x3fe3ce53d12162a0ULL, 0x3fe36dd2e26d8202ULL,
  0x3fe30c9aa526da4bULL, 0x3fe2aa9ee123680bULL, 0x3fe247d26538ff2eULL, 0x3fe1e426e93e49e7ULL,
  0x3fe17f8ceb4bdfa0ULL, 0x3fe119f38749f5afULL, 0x3fe0b348479b80fcULL, 0x3fe04b76ed6a7558ULL,
  0x3fdfc4d25d683209ULL, 0x3fdef00ccf5f4faaULL, 0x3fde186678f1735aULL, 0x3fdd3da24df17c36ULL,
  0x3fdc5f7bd78c3f89ULL, 0x3fdb7da5dddda3c4ULL, 0x3fda97c8be5d5204ULL, 0x3fd9ad80552237d2ULL,
  0x3fd8be5954d3606fULL, 0x3fd7c9cdda17d019ULL, 0x3fd6cf40f0a72bbdULL, 0x3fd5cdf89d024ac3ULL,
  0x3fd4c515c60bfe22ULL, 0x3fd3b388fe3d6ecaULL, 0x3fd2980290da2633ULL, 0x3fd170db24d6f670ULL,
  0x3fd03bf049c65c3cULL, 0x3fcdecd8b76dbd98ULL, 0x3fcb38d1ef79b7ccULL, 0x3fc85090fbc27a80ULL,
  0x3fc522e6e54a2a74ULL, 0x3fc19335a95b8dbaULL, 0x3fbad6b2495b4d2cULL, 0x3fb0589d8b5d411bULL,
  0x0000000000000000ULL};
static const uint64_t ZF[257] = {
  0x3f25e5d3f59d055cULL, 0x3f3dc31c329f0b4bULL, 0x3f4fb20af78dfcb9ULL, 0x3f592bb5540c3e25ULL,
  0x3f61946ba8e1a324ULL, 0x3f66d888f3a1feffULL, 0x3f6c58b381cd4b11ULL, 0x3f71073d69574043ULL,
  0x3f73fa97cee322fdULL, 0x3f77049f37ec3620ULL, 0x3f7a23e9d4974836ULL, 0x3f7d5751fa745dc5ULL,
  0x3f804ef2295fd7f9ULL, 0x3f81fb69edb37671ULL, 0x3f83b0b8c1516f62ULL, 0x3f856e930be416cbULL,
  0x3f8734b6e6aa74f5ULL, 0x3f8902ea688fa7bdULL, 0x3f8ad8fa5542c92dULL, 0x3f8cb6b9146e2757ULL,
  0x3f8e9bfdde89c7ceULL, 0x3f904452091e02f0ULL, 0x3f913e4554725f5fULL, 0x3f923bc9e1b93a32ULL,
  0x3f933cd225315d84ULL, 0x3f944151ce87f0beULL, 0x3f95493da6ab0251ULL, 0x3f96548b72a24077ULL,
  0x3f976331da87fc96ULL, 0x3f98752853ec9967ULL, 0x3f998a670f132a48ULL, 0x3f9aa2e6e6924e9bULL,
  0x3f9bbea150fa5870ULL, 0x3f9cdd9054331b0cULL, 0x3f9dffae7a517468ULL, 0x3f9f24f6c7af9890ULL,
  0x3fa026b2590dfaeeULL, 0x3fa0bc7a0c7cd651ULL, 0x3fa153d09f19b3a1ULL, 0x3fa1ecb45ff312d4ULL,
  0x3fa28723c956c00cULL, 0x3fa3231d7e3f14aeULL, 0x3fa3c0a047ff18ffULL, 0x3fa45fab14266b19ULL,
  0x3fa5003cf296c5ebULL, 0x3fa5a25513c5d2caULL, 0x3fa645f2c726a041ULL, 0x3fa6eb1579b6af52ULL,
  0x3fa791bcb4ab089eULL, 0x3fa839e81c3a396bULL, 0x3fa8e3976e80776dULL, 0x3fa98eca827b7c4cULL,
  0x3faa3b81471bf138ULL, 0x3faae9bbc26a8084ULL, 0x3fab997a10bed985ULL, 0x3fac4abc640721e9ULL,
  0x3facfd83031e794aULL, 0x3fadb1ce49315810ULL, 0x3fae679ea52eb2e5ULL, 0x3faf1ef49944e834ULL,
  0x3fafd7d0ba699676ULL, 0x3fb04919d7f5c817ULL, 0x3fb0a70f19871b3bULL, 0x3fb105c88756ca50ULL,
  0x3fb165468f755392ULL, 0x3fb1c589a86fa340ULL, 0x3fb22692512c9d8cULL, 0x3fb2886110ce0570ULL,
  0x3fb2eaf676948dd1ULL, 0x3fb34e5319c6e718ULL, 0x3fb3b277999b9f9eULL, 0x3fb417649d25b10eULL,
  0x3fb47d1ad343985cULL, 0x3fb4e39af290d929ULL, 0x3fb54ae5b959d036ULL, 0x3fb5b2fbed91bb3eULL,
  0x3fb61bde5ccadef7ULL, 0x3fb6858ddc30b620ULL, 0x3fb6f00b488416b6ULL, 0x3fb75b5786193c1eULL,
  0x3fb7c77380d7a6f3ULL, 0x3fb834602c3bc4baULL, 0x3fb8a21e835a533bULL, 0x3fb910af88e574b9ULL,
  0x3fb9801447336b70ULL, 0x3fb9f04dd046f428ULL, 0x3fba615d3dd938b7ULL, 0x3fbad343b1655465ULL,
  0x3fbb460254356548ULL, 0x3fbbb99a5771268fULL, 0x3fbc2e0cf42e10afULL, 0x3fbca35b6b80fd57ULL,
  0x3fbd198706914dd7ULL, 0x3fbd909116ad9398ULL, 0x3fbe087af561bafbULL, 0x3fbe8146048eb9ccULL,
  0x3fbefaf3ae83c33cULL, 0x3fbf758566190414ULL, 0x3fbff0fca6cbea8dULL, 0x3fc036ad7a6e7f04ULL,
  0x3fc07550eeb7a5beULL, 0x3fc0b4697b54b62fULL, 0x3fc0f3f7efec1720ULL, 0x3fc133fd20c9712fULL,
  0x3fc17479e6f0ae78ULL, 0x3fc1b56f2031d666ULL, 0x3fc1f6ddaf3dca65ULL, 0x3fc238c67bbbe878ULL,
  0x3fc27b2a72609940ULL, 0x3fc2be0a8504cf34ULL, 0x3fc30167aabe7d6eULL, 0x3fc34542dffa0cafULL,
  0x3fc3899d2694d5c9ULL, 0x3fc3ce7785f8a905ULL, 0x3fc413d30b386a9aULL, 0x3fc459b0c92dccc6ULL,
  0x3fc4a011d8983096ULL, 0x3fc4e6f7583cb6faULL, 0x3fc52e626d078c49ULL, 0x3fc57654422e78f5ULL,
  0x3fc5bece0954c2b6ULL, 0x3fc607d0fab06a31ULL, 0x3fc6515e5530d1acULL, 0x3fc69b775ea6da28ULL,
  0x3fc6e61d63ee84eaULL, 0x3fc73151b91a2839ULL, 0x3fc77d15b99f46feULL, 0x3fc7c96ac8851baeULL,
  0x3fc816525094e7e6ULL, 0x3fc863cdc48c1af9ULL, 0x3fc8b1de9f5062d5ULL, 0x3fc900866425bb79ULL,
  0x3fc94fc69ee692a1ULL, 0x3fc99fa0e43e1623ULL, 0x3fc9f016d1e4c512ULL, 0x3fca412a0edf5cbcULL,
  0x3fca92dc4bc03c49ULL, 0x3fcae52f42eb5b0bULL, 0x3fcb3824b8dcef3eULL, 0x3fcb8bbe7c72e4a5ULL,
  0x3fcbdffe67394435ULL, 0x3fcc34e65db9afeeULL, 0x3fcc8a784fce1801ULL, 0x3fcce0b638f6d09fULL,
  0x3fcd37a220b431fdULL, 0x3fcd8f3e1ae3eeb8ULL, 0x3fcde78c48224f39ULL, 0x3fce408ed62f83a7ULL,
  0x3fce9a48005940f2ULL, 0x3fcef4ba0fe8e09bULL, 0x3fcf4fe75c963e7eULL, 0x3fcfabd24cff9354ULL,
  0x3fd0043eab93476aULL, 0x3fd032f580797c2cULL, 0x3fd0620ef05d90d2ULL, 0x3fd0918c4ee93e13ULL,
  0x3fd0c16ef88f5333ULL, 0x3fd0f1b852d9a66cULL, 0x3fd12269ccba9fbaULL, 0x3fd15384dee291efULL,
  0x3fd1850b0c191982ULL, 0x3fd1b6fde19abc5aULL, 0x3fd1e95ef77b09dbULL, 0x3fd21c2ff10b7effULL,
  0x3fd24f727d4776fdULL, 0x3fd2832857457629ULL, 0x3fd2b75346ae2262ULL, 0x3fd2ebf520394270ULL,
  0x3fd3210fc6312435ULL, 0x3fd356a528fcd0ddULL, 0x3fd38cb747b17defULL, 0x3fd3c34830abb285ULL,
  0x3fd3fa5a0230a14eULL, 0x3fd431eeeb1841e2ULL, 0x3fd46a092b80beefULL, 0x3fd4a2ab158bdad3ULL,
  0x3fd4dbd70e26f91dULL, 0x3fd5158f8dde89f5ULL, 0x3fd54fd721bda3e7ULL, 0x3fd58ab06c3aa9efULL,
  0x3fd5c61e2631ee6cULL, 0x3fd602231fef5876ULL, 0x3fd63ec2424827e4ULL, 0x3fd67bfe8fc60d9fULL,
  0x3fd6b9db25e4e99cULL, 0x3fd6f85b3e649e9dULL, 0x3fd7378230b08deaULL, 0x3fd77753735e72e3ULL,
  0x3fd7b7d29dc6801eULL, 0x3fd7f90369b6ce59ULL, 0x3fd83ae9b5446138ULL, 0x3fd87d8984bc3f8cULL,
  0x3fd8c0e704b75d39ULL, 0x3fd905068c545d04ULL, 0x3fd949ec9f9a8110ULL, 0x3fd98f9df2097ba8ULL,
  0x3fd9d61f695a3792ULL, 0x3fda1d76207521f4ULL, 0x3fda65a76aa30140ULL, 0x3fdaaeb8d6fdf6e5ULL,
  0x3fdaf8b03428ef5fULL, 0x3fdb43939454806fULL, 0x3fdb8f6951990b88ULL, 0x3fdbdc3812aeeeb5ULL,
  0x3fdc2a06d00ea583ULL, 0x3fdc78dcd983fb60ULL, 0x3fdcc8c1dc40e092ULL, 0x3fdd19bde97e1a0bULL,
  0x3fdd6bd97db9ed7aULL, 0x3fddbf1d88a7210cULL, 0x3fde139375e137fcULL, 0x3fde6945367dd351ULL,
  0x3fdec03d4b969d90ULL, 0x3fdf1886d1eb424dULL, 0x3fdf722d8ebfc5faULL, 0x3fdfcd3dfe214576ULL,
  0x3fe014e2b160f324ULL, 0x3fe043e8ebd26548ULL, 0x3fe073b931ee3b7dULL, 0x3fe0a45b8854d02aULL,
  0x3fe0d5d8812b1e2bULL, 0x3fe108394a1cc38cULL, 0x3fe13b87bc33169cULL, 0x3fe16fce6dce6feeULL,
  0x3fe1a518c71e3b25ULL, 0x3fe1db7319877b89ULL, 0x3fe212eaba813ec8ULL, 0x3fe24b8e228c50a3ULL,
  0x3fe2856d111132bdULL, 0x3fe2c098b61f4f24ULL, 0x3fe2fd23e345da5eULL, 0x3fe33b23450e6318ULL,
  0x3fe37aada708ddd9ULL, 0x3fe3bbdc44e1d114ULL, 0x3fe3fecb2bb18b7fULL, 0x3fe44399afa8e125ULL,
  0x3fe48a6afb8ee069ULL, 0x3fe4d366c151f8aeULL, 0x3fe51eba1578899aULL, 0x3fe56c9882da8773ULL,
  0x3fe5bd3d694cac75ULL, 0x3fe610edc1a7af66ULL, 0x3fe667fa6d4f5c06ULL, 0x3fe6c2c3498418c6ULL,
  0x3fe721bb5ba94b63ULL, 0x3fe7856e9b09d47eULL, 0x3fe7ee8a2d243126ULL, 0x3fe85de87806c5b8ULL,
  0x3fe8d4a376d3d22fULL, 0x3fe95431c455aa39ULL, 0x3fe9de9715556d9bULL, 0x3fea76baa562fae7ULL,
  0x3feb210f0ee67f2aULL, 0x3febe5007beb7b27ULL, 0x3fecd0a65081fff0ULL, 0x3fee0545e5881137ULL,
  0x3ff0000000000000ULL};
static double X[257], F[257];
static inline double neglogword(uint64_t w) { return -log(((double)(w >> 12) + 0.5) * P52); }
// The slow path after a draw at x in layer i, with two further words (see HostFloat.lean).
static double zigslow(unsigned i, double x, uint64_t w2, uint64_t w3) {
  if (i == 0) return X[1] + neglogword(w2);
  double v = (double)(w2 >> 11) * P53;
  if (F[i + 1] + (F[i] - F[i + 1]) * v < exp(-x)) return x;
  return neglogword(w3);
}
static inline double expo(void) {
  uint64_t w = next();
  unsigned i = (unsigned)(w & 255);
  double x = ((double)(w >> 12) + 0.5) * P52 * X[i];
  if (x < X[i + 1]) return x;
  uint64_t w2 = next(), w3 = next();
  return zigslow(i, x, w2, w3);
}

static int S, M, depth, leaves;
static long *pop, *lo, *hi, *ms;
static Rx *rx;
static int **deps, *ndeps;
static double *lower, *tree;

static inline unsigned long ff(unsigned long n, int nu) {
  unsigned long r = 1;
  for (int k = 0; k < nu; k++) { if (n < (unsigned long)(k + 1)) return 0; r *= (n - k); }
  return r;
}
static inline double prop(const Rx *r, const long *arr) {
  unsigned long c = 1;
  for (int i = 0; i < r->nr; i++) c *= ff((unsigned long)arr[r->rs[i]], r->rn[i]);
  return r->rate * (double)c;
}
static void bracket(long m, long n, long *l, long *h) {
  if (n == 0) { *l = 0; *h = 0; }
  else if (n < m) { *l = n; *h = n; }
  else if (n < 25) { *l = n >= 4 ? n - 4 : 0; *h = n + 4; }
  else { *l = 9 * n / 10; *h = 11 * n / 10; }
}
static inline int stale(long m, long n, long l, long h) { return n < l || h < n || (n < m && h != n); }

int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r");
  double T = atof(argv[2]);
  uint64_t seed = argc > 3 ? strtoull(argv[3], 0, 10) : 1;
  char tag[64];
  if (fscanf(f, "%63s %*d", tag) != 1) return 1;
  if (fscanf(f, "%63s %d", tag, &S) != 2) return 1;
  pop = calloc(S, sizeof(long)); lo = calloc(S, sizeof(long)); hi = calloc(S, sizeof(long));
  ms = calloc(S, sizeof(long));
  for (int s = 0; s < S; s++) if (fscanf(f, "%ld", &pop[s]) != 1) return 1;
  if (fscanf(f, "%63s %d", tag, &M) != 2) return 1;
  rx = calloc(M, sizeof(Rx));
  for (int j = 0; j < M; j++) {
    char hex[32]; uint64_t bits;
    if (fscanf(f, "%31s", hex) != 1) return 1;
    bits = strtoull(hex, 0, 16); memcpy(&rx[j].rate, &bits, 8);
    if (fscanf(f, "%d", &rx[j].nr) != 1) return 1;
    rx[j].rs = calloc(rx[j].nr + 1, sizeof(int)); rx[j].rn = calloc(rx[j].nr + 1, sizeof(int));
    for (int i = 0; i < rx[j].nr; i++) if (fscanf(f, "%d %d", &rx[j].rs[i], &rx[j].rn[i]) != 2) return 1;
    if (fscanf(f, "%d", &rx[j].nc) != 1) return 1;
    rx[j].cs = calloc(rx[j].nc + 1, sizeof(int)); rx[j].cd = calloc(rx[j].nc + 1, sizeof(long));
    for (int i = 0; i < rx[j].nc; i++) if (fscanf(f, "%d %ld", &rx[j].cs[i], &rx[j].cd[i]) != 2) return 1;
    for (int i = 0; i < rx[j].nr; i++) if (rx[j].rn[i] > ms[rx[j].rs[i]]) ms[rx[j].rs[i]] = rx[j].rn[i];
  }
  deps = calloc(S, sizeof(int *)); ndeps = calloc(S, sizeof(int));
  for (int j = 0; j < M; j++) for (int i = 0; i < rx[j].nr; i++) ndeps[rx[j].rs[i]]++;
  for (int s = 0; s < S; s++) { deps[s] = calloc(ndeps[s] + 1, sizeof(int)); ndeps[s] = 0; }
  for (int j = 0; j < M; j++) for (int i = 0; i < rx[j].nr; i++) { int s = rx[j].rs[i]; deps[s][ndeps[s]++] = j; }
  depth = 0; { unsigned m = M - 1; int lg = 0; while (m >>= 1) lg++; depth = lg + 1; }
  if (M <= 1) depth = 1;
  leaves = 1 << depth;
  for (int s = 0; s < S; s++) bracket(ms[s], pop[s], &lo[s], &hi[s]);
  lower = calloc(M, sizeof(double)); tree = calloc(2 * leaves, sizeof(double));
  memcpy(X, ZX, sizeof X); memcpy(F, ZF, sizeof F);
  uint64_t x = seed; s0 = splitmix(&x); s1 = splitmix(&x); s2 = splitmix(&x); s3 = splitmix(&x);
  struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
  for (int j = 0; j < M; j++) { lower[j] = prop(&rx[j], lo); tree[leaves + j] = prop(&rx[j], hi); }
  for (int k = leaves - 1; k >= 1; k--) tree[k] = tree[2 * k] + tree[2 * k + 1];
  double now = 0; long events = 0;
  for (;;) {
    double total = tree[1];
    if (!(total > 0)) break;
    double elapsed = 0; int j;
    for (;;) {
      double u = (double)(next() >> 11) * P53;
      double xx = u * total; int k = 1;
      for (int d = 0; d < depth; d++) { double l = tree[2 * k]; if (xx < l) k = 2 * k; else { k = 2 * k + 1; xx -= l; } }
      j = k - leaves;
      double e = expo();
      elapsed += e;
      double v = (double)(next() >> 11) * P53;
      if (j < M) {
        double th = v * tree[leaves + j], l = lower[j];
        if ((0 < l && th <= l)) break;
        double a = prop(&rx[j], pop);
        if (0 < a && th <= a) break;
      }
    }
    double t = now + elapsed / total;
    if (t > T) break;
    now = t; events++;
    for (int i = 0; i < rx[j].nc; i++) { long *p = &pop[rx[j].cs[i]]; *p = *p + rx[j].cd[i]; if (*p < 0) *p = 0; }
    for (int i = 0; i < rx[j].nc; i++) {
      int s = rx[j].cs[i];
      if (stale(ms[s], pop[s], lo[s], hi[s])) {
        bracket(ms[s], pop[s], &lo[s], &hi[s]);
        for (int q = 0; q < ndeps[s]; q++) {
          int kk = deps[s][q];
          lower[kk] = prop(&rx[kk], lo);
          double up = prop(&rx[kk], hi);
          int leaf = leaves + kk;
          if (up != tree[leaf] || signbit(up) != signbit(tree[leaf])) {
            tree[leaf] = up;
            for (int n = leaf / 2; n >= 1; n /= 2) tree[n] = tree[2 * n] + tree[2 * n + 1];
          }
        }
      }
    }
  }
  clock_gettime(CLOCK_MONOTONIC, &t1);
  double secs = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
  uint64_t h = 0xcbf29ce484222325ULL;
  for (int s = 0; s < S; s++) h = (h ^ (uint64_t)pop[s]) * 0x100000001b3ULL;
  printf("{\"events\": %ld, \"seconds\": %.6f, \"rate\": %.4g, \"digest\": \"%llu\"}\n", events, secs,
         events / secs, (unsigned long long)h);
  return 0;
}
