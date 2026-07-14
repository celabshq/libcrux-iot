# ML-KEM / ML-DSA Stack Usage

Measurements taken at revision `95a43e554866d4eb2db411c066ca0fb528eddbfd`.

## ML-KEM

| Parameter set | Key Generation (bytes) | Encapsulation (bytes) | Decapsulation (bytes) |
|---------------|------------------------|-----------------------|-----------------------|
| ML-KEM 512    | 17120                  | 13512                 | 15272                 |
| ML-KEM 768    | 24744                  | 16344                 | 18872                 |
| ML-KEM 1024   | 33816                  | 19864                 | 23160                 |

## ML-DSA (stack-optimized)

| Parameter set | Key Generation (bytes) | Signing (bytes) | Verification (bytes) |
|---------------|------------------------|-----------------|----------------------|
| ML-DSA 44     | 45952                  | 78896           | 9232                 |
| ML-DSA 65     | 71568                  | 117584          | 9224                 |
| ML-DSA 87     | 109400                 | 168184          | 9232                 |
