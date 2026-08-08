# Benchmark Results

Results captured on the reference board.

## Cycle Measurements

To run ML-KEM measurements:
```
cd libcrux-nucleo-l4r5zi
# $variant in {mlkem512, mlkem768, mlkem1024}
DEFMT_LOG=info cargo rrb mlkem --no-default-features -F $variant,mldsa44
```

To run ML-DSA measurements:

```
cd libcrux-nucleo-l4r5zi
# $variant in {mldsa44, mldsa65, mldsa87}
DEFMT_LOG=info cargo rrb mldsa --no-default-features -F $variant,mlkem512
```

### ML-KEM 512
```
l,0,16000000,ML-KEM Benchmark
b,r,bench_keygen,0
b,d,bench_keygen,0,690156
b,r,bench_keygen,1
b,d,bench_keygen,1,690150
b,r,bench_keygen,2
b,d,bench_keygen,2,690157
b,r,bench_keygen,3
b,d,bench_keygen,3,690150
b,r,bench_keygen,4
b,d,bench_keygen,4,690150
b,r,bench_encaps,0
b,d,bench_encaps,0,736112
b,r,bench_encaps,1
b,d,bench_encaps,1,736103
b,r,bench_encaps,2
b,d,bench_encaps,2,736115
b,r,bench_encaps,3
b,d,bench_encaps,3,736103
b,r,bench_encaps,4
b,d,bench_encaps,4,736117
b,r,bench_decaps,0
b,d,bench_decaps,0,852716
b,r,bench_decaps,1
b,d,bench_decaps,1,852730
b,r,bench_decaps,2
b,d,bench_decaps,2,852716
b,r,bench_decaps,3
b,d,bench_decaps,3,852725
b,r,bench_decaps,4
b,d,bench_decaps,4,852716
Firmware exited successfully
```

### ML-KEM 768

```
l,0,16000000,ML-KEM Benchmark
b,r,bench_keygen,0
b,d,bench_keygen,0,1103324
b,r,bench_keygen,1
b,d,bench_keygen,1,1103324
b,r,bench_keygen,2
b,d,bench_keygen,2,1103328
b,r,bench_keygen,3
b,d,bench_keygen,3,1103320
b,r,bench_keygen,4
b,d,bench_keygen,4,1103326
b,r,bench_encaps,0
b,d,bench_encaps,0,1196687
b,r,bench_encaps,1
b,d,bench_encaps,1,1196684
b,r,bench_encaps,2
b,d,bench_encaps,2,1196692
b,r,bench_encaps,3
b,d,bench_encaps,3,1196688
b,r,bench_encaps,4
b,d,bench_encaps,4,1196687
b,r,bench_decaps,0
b,d,bench_decaps,0,1353693
b,r,bench_decaps,1
b,d,bench_decaps,1,1353704
b,r,bench_decaps,2
b,d,bench_decaps,2,1353700
b,r,bench_decaps,3
b,d,bench_decaps,3,1353695
b,r,bench_decaps,4
b,d,bench_decaps,4,1353693
Firmware exited successfully
```

### ML-KEM 1024

```
l,0,16000000,ML-KEM Benchmark
b,r,bench_keygen,0
b,d,bench_keygen,0,1716659
b,r,bench_keygen,1
b,d,bench_keygen,1,1716659
b,r,bench_keygen,2
b,d,bench_keygen,2,1716659
b,r,bench_keygen,3
b,d,bench_keygen,3,1716662
b,r,bench_keygen,4
b,d,bench_keygen,4,1716659
b,r,bench_encaps,0
b,d,bench_encaps,0,1833362
b,r,bench_encaps,1
b,d,bench_encaps,1,1833364
b,r,bench_encaps,2
b,d,bench_encaps,2,1833365
b,r,bench_encaps,3
b,d,bench_encaps,3,1833363
b,r,bench_encaps,4
b,d,bench_encaps,4,1833359
b,r,bench_decaps,0
b,d,bench_decaps,0,2027928
b,r,bench_decaps,1
b,d,bench_decaps,1,2027933
b,r,bench_decaps,2
b,d,bench_decaps,2,2027933
b,r,bench_decaps,3
b,d,bench_decaps,3,2027933
b,r,bench_decaps,4
b,d,bench_decaps,4,2027932
Firmware exited successfully
```

### ML-DSA 44

```
l,0,16000000,ML-DSA Benchmark
b,r,bench_keygen,0
b,d,bench_keygen,0,2907973
b,r,bench_keygen,1
b,d,bench_keygen,1,2907975
b,r,bench_keygen,2
b,d,bench_keygen,2,2907974
b,r,bench_keygen,3
b,d,bench_keygen,3,2907972
b,r,bench_keygen,4
b,d,bench_keygen,4,2907975
b,r,bench_sign,0
b,d,bench_sign,0,3834740
b,r,bench_sign,1
b,d,bench_sign,1,3834744
b,r,bench_sign,2
b,d,bench_sign,2,3834741
b,r,bench_sign,3
b,d,bench_sign,3,3834744
b,r,bench_sign,4
b,d,bench_sign,4,3834746
b,r,bench_verify,0
b,d,bench_verify,0,2560836
b,r,bench_verify,1
b,d,bench_verify,1,2560838
b,r,bench_verify,2
b,d,bench_verify,2,2560837
b,r,bench_verify,3
b,d,bench_verify,3,2560836
b,r,bench_verify,4
b,d,bench_verify,4,2560839
Firmware exited successfully
```

### ML-DSA 65

```
l,0,16000000,ML-DSA Benchmark
b,r,bench_keygen,0
b,d,bench_keygen,0,4548147
b,r,bench_keygen,1
b,d,bench_keygen,1,4548143
b,r,bench_keygen,2
b,d,bench_keygen,2,4548147
b,r,bench_keygen,3
b,d,bench_keygen,3,4548146
b,r,bench_keygen,4
b,d,bench_keygen,4,4548144
b,r,bench_sign,0
b,d,bench_sign,0,5609316
b,r,bench_sign,1
b,d,bench_sign,1,5609313
b,r,bench_sign,2
b,d,bench_sign,2,5609311
b,r,bench_sign,3
b,d,bench_sign,3,5609316
b,r,bench_sign,4
b,d,bench_sign,4,5609313
b,r,bench_verify,0
b,d,bench_verify,0,4240913
b,r,bench_verify,1
b,d,bench_verify,1,4240920
b,r,bench_verify,2
b,d,bench_verify,2,4240919
b,r,bench_verify,3
b,d,bench_verify,3,4240916
b,r,bench_verify,4
b,d,bench_verify,4,4240921
Firmware exited successfully
```

### ML-DSA 87

```
l,0,16000000,ML-DSA Benchmark
b,r,bench_keygen,0
b,d,bench_keygen,0,7786305
b,r,bench_keygen,1
b,d,bench_keygen,1,7786304
b,r,bench_keygen,2
b,d,bench_keygen,2,7786303
b,r,bench_keygen,3
b,d,bench_keygen,3,7786306
b,r,bench_keygen,4
b,d,bench_keygen,4,7786306
b,r,bench_sign,0
b,d,bench_sign,0,13558244
b,r,bench_sign,1
b,d,bench_sign,1,13558242
b,r,bench_sign,2
b,d,bench_sign,2,13558238
b,r,bench_sign,3
b,d,bench_sign,3,13558242
b,r,bench_sign,4
b,d,bench_sign,4,13558240
b,r,bench_verify,0
b,d,bench_verify,0,7210660
b,r,bench_verify,1
b,d,bench_verify,1,7210655
b,r,bench_verify,2
b,d,bench_verify,2,7210655
b,r,bench_verify,3
b,d,bench_verify,3,7210657
b,r,bench_verify,4
b,d,bench_verify,4,7210654
Firmware exited successfully
```


## Stack usage

Results in bytes on the reference board.
Run `./measure-stacks.sh` in `libcrux-nucleo-l4r5zi` to reproduce.

```
Repository at commit: 9218c076a08d4fb9697e4e615c049a576ea78c4f
l,0,0,ML-KEM 1024 Key Generation
b,r,stack,0
b,d,stack,0,34016
Firmware exited successfully
l,0,0,ML-KEM 1024 Encapsulation
b,r,stack,0
b,d,stack,0,20104
Firmware exited successfully
l,0,0,ML-KEM 1024 Decapsulation
b,r,stack,0
b,d,stack,0,23400
Firmware exited successfully
l,0,0,ML-DSA 87 Key Generation
b,r,stack,0
b,d,stack,0,109464
Firmware exited successfully
l,0,0,ML-DSA 87 Signing
b,r,stack,0
b,d,stack,0,168192
Firmware exited successfully
l,0,0,ML-DSA 87 Verification
b,r,stack,0
b,d,stack,0,9760
Firmware exited successfully
```



