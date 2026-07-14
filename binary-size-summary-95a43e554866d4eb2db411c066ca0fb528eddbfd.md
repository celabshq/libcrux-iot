# libcrux-iot binary size report

Section sizes (bytes) of the `libcrux-iot-binary-size` firmware built for `thumbv7em-none-eabihf`.

`flash total` = .gnu.sgstubs + .rodata + .text + .vector_table; `RAM` = .bss + .data + .uninit.

### ml-kem

| variant   | operation    | profile       |  .text | .rodata | flash total | RAM | size total |
|-----------|--------------|---------------|-------:|--------:|------------:|----:|-----------:|
| mlkem512  | mlkem-keygen | release       | 63,000 |     256 |      64,280 |   0 |     64,477 |
| mlkem512  | mlkem-keygen | release-small | 48,184 |     256 |      49,464 |   0 |     49,659 |
| mlkem512  | mlkem-encaps | release       | 80,212 |     256 |      81,492 |   0 |     81,689 |
| mlkem512  | mlkem-encaps | release-small | 54,660 |     256 |      55,940 |   0 |     56,135 |
| mlkem512  | mlkem-decaps | release       | 95,556 |     256 |      96,836 |   0 |     97,033 |
| mlkem512  | mlkem-decaps | release-small | 60,448 |     256 |      61,728 |   0 |     61,923 |
| mlkem768  | mlkem-keygen | release       | 61,128 |     256 |      62,408 |   0 |     62,605 |
| mlkem768  | mlkem-keygen | release-small | 48,272 |     256 |      49,552 |   0 |     49,747 |
| mlkem768  | mlkem-encaps | release       | 79,628 |     256 |      80,908 |   0 |     81,105 |
| mlkem768  | mlkem-encaps | release-small | 54,880 |     256 |      56,160 |   0 |     56,355 |
| mlkem768  | mlkem-decaps | release       | 96,060 |     256 |      97,340 |   0 |     97,537 |
| mlkem768  | mlkem-decaps | release-small | 60,624 |     256 |      61,904 |   0 |     62,099 |
| mlkem1024 | mlkem-keygen | release       | 61,692 |     256 |      62,972 |   0 |     63,169 |
| mlkem1024 | mlkem-keygen | release-small | 48,320 |     256 |      49,600 |   0 |     49,795 |
| mlkem1024 | mlkem-encaps | release       | 81,032 |     256 |      82,312 |   0 |     82,509 |
| mlkem1024 | mlkem-encaps | release-small | 55,060 |     256 |      56,340 |   0 |     56,535 |
| mlkem1024 | mlkem-decaps | release       | 97,628 |     256 |      98,908 |   0 |     99,105 |
| mlkem1024 | mlkem-decaps | release-small | 60,504 |     256 |      61,784 |   0 |     61,979 |

### ml-dsa

| variant | operation    | profile       |   .text | .rodata | flash total | RAM | size total |
|---------|--------------|---------------|--------:|--------:|------------:|----:|-----------:|
| mldsa44 | mldsa-keygen | release       |  99,352 |   2,040 |     102,416 |   0 |    102,611 |
| mldsa44 | mldsa-keygen | release-small |  57,424 |   2,040 |      60,488 |   0 |     60,683 |
| mldsa44 | mldsa-sign   | release       | 119,224 |   2,040 |     122,288 |   0 |    122,483 |
| mldsa44 | mldsa-sign   | release-small |  59,000 |   2,040 |      62,064 |   0 |     62,259 |
| mldsa44 | mldsa-verify | release       |  96,696 |   2,040 |      99,760 |   0 |     99,955 |
| mldsa44 | mldsa-verify | release-small |  53,732 |   2,040 |      56,796 |   0 |     56,991 |
| mldsa65 | mldsa-keygen | release       |  97,668 |   2,040 |     100,732 |   0 |    100,927 |
| mldsa65 | mldsa-keygen | release-small |  59,164 |   2,040 |      62,228 |   0 |     62,423 |
| mldsa65 | mldsa-sign   | release       | 119,268 |   2,040 |     122,332 |   0 |    122,527 |
| mldsa65 | mldsa-sign   | release-small |  58,960 |   2,040 |      62,024 |   0 |     62,219 |
| mldsa65 | mldsa-verify | release       |  95,076 |   2,040 |      98,140 |   0 |     98,335 |
| mldsa65 | mldsa-verify | release-small |  53,728 |   2,040 |      56,792 |   0 |     56,987 |
| mldsa87 | mldsa-keygen | release       |  98,596 |   2,040 |     101,660 |   0 |    101,855 |
| mldsa87 | mldsa-keygen | release-small |  59,352 |   2,040 |      62,416 |   0 |     62,611 |
| mldsa87 | mldsa-sign   | release       | 123,436 |   2,040 |     126,500 |   0 |    126,695 |
| mldsa87 | mldsa-sign   | release-small |  58,376 |   2,040 |      61,440 |   0 |     61,635 |
| mldsa87 | mldsa-verify | release       |  96,404 |   2,040 |      99,468 |   0 |     99,663 |
| mldsa87 | mldsa-verify | release-small |  53,240 |   2,040 |      56,304 |   0 |     56,499 |

