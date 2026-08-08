/* Memory layout for `qemu-system-arm -M mps2-an386`. */
MEMORY
{
    FLASH : ORIGIN = 0x00000000, LENGTH = 4096K
    RAM   : ORIGIN = 0x20000000, LENGTH =  640K
}
