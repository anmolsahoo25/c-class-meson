project('c-class-meson')

options = [
'-verilog',
'-vdir', '@OUTDIR@',
'-bdir', '@OUTDIR@',
'-D', 'RV64=True',
'-D', 'atomic=True',
'-D', 'spfpu=True',
'-D', 'dpfpu=True',
'-D', 'compressed=True',
'-D', 'muldiv=True',
'-D', 'simulate=True',
'-D', 'user=True',
'-D', 'rtldump=True',
'-D', 'supervisor=True',
'-D', 'sv39',
'-D', 'ASSERT=True',
'-D', 'icache=True',
'-D', 'dcache=True',
'-D', 'dtim ',
'-D', 'itim',
'-D', 'bpu=True',
'-D', 'ifence=True',
'-D', 'bpu_ras',
'-D', 'csr_low_latency=True',
'-D', 'perfmonitors=True',
'-D', 'csr_grp4=True',
'-D', 'csr_grp5=True',
'-D', 'csr_grp6=True',
'-D', 'csr_grp7=True',
'-D', 'counters_size=29',
'-D', 'CORE_AXI4=True',
'-D', 'MULSTAGES=2',
'-D', 'DIVSTAGES=32',
'-D', 'counters_grp4=7',
'-D', 'counters_grp5=7',
'-D', 'counters_grp6=7',
'-D', 'counters_grp7=8',
'-D', 'Addr_space=25',
'-D', 'iwords=4',
'-D', 'iblocks=16',
'-D', 'iways=4',
'-D', 'isets=64',
'-D', 'ifbsize=4',
'-D', 'irepl=PLRU',
'-D', 'icachereset=1',
'-D', 'iesize=2',
'-D', 'idbanks=1',
'-D', 'itbanks=1',
'-D', 'ddbanks=1',
'-D', 'dtbanks=1',
'-D', 'dwords=8',
'-D', 'dblocks=8',
'-D', 'dways=4',
'-D', 'dsets=64',
'-D', 'dfbsize=8',
'-D', 'drepl=PLRU',
'-D', 'dcachereset=1',
'-D', 'desize=1',
'-D', 'dsbsize=2',
'-D', 'ibuswidth=64',
'-D', 'paddr=32',
'-D', 'vaddr=64',
'-D', 'PMPSIZE=0',
'-D', 'resetpc=4096',
'-D', 'asidwidth=9',
'-D', 'DTVEC_BASE=0000',
'-D', 'btbdepth=32',
'-D', 'bhtdepth=512',
'-D', 'histlen=8',
'-D', 'extrahist=3',
'-D', 'rasdepth=8',
'-D', 'bpureset=1',
'-D', 'causesize=6',
'-D', 'gshare=True',
'-D', 'itlbsize=4',
'-D', 'dtlbsize=4',
'-D', 'dtim_banks=1',
'-D', 'itim_banks=1',
'-D', 'dtimbase=1879048192',
'-D', 'dtimbound=1879052288',
'-D', 'itimbase=268435456',
'-D', 'itimbound=268439552',
'+RTS',
'-K40000M',
'-RTS',
'-check-assert',
'-keep-fires',
'-opt-undetermined-vals',
'-remove-false-rules',
'-remove-empty-rules',
'-remove-starved-rules',
'-remove-dollar',
'-unspecified-to', 'X'
]

bsc = find_program('bsc')
cat = find_program('cat')

# includes

sdram_defines = custom_target('sdram_defines',
input : './include/sdram.defines',
output : 'sdram.defines',
command : [cat , '@INPUT@'],
capture : true)

common_params_bsv = custom_target('common_params_bsv',
input : './include/common_params.bsv',
output : 'common_params.bsv',
command : [cat , '@INPUT@'],
capture : true)

uart_defines = custom_target('uart_defines',
input : './include/uart.defines',
output : 'uart.defines',
command : [cat , '@INPUT@'],
capture : true)

pwm_defines = custom_target('pwm_defines',
input : './include/pwm.defines',
output : 'pwm.defines',
command : [cat , '@INPUT@'],
capture : true)

plic_defines = custom_target('plic_defines',
input : './include/plic.defines',
output : 'plic.defines',
command : [cat , '@INPUT@'],
capture : true)

log_txt = custom_target('log_txt',
input : './include/log.txt',
output : 'log.txt',
command : [cat , '@INPUT@'],
capture : true)

clint_defines = custom_target('clint_defines',
input : './include/clint.defines',
output : 'clint.defines',
command : [cat , '@INPUT@'],
capture : true)

qspi_defines = custom_target('qspi_defines',
input : './include/qspi.defines',
output : 'qspi.defines',
command : [cat , '@INPUT@'],
capture : true)

Soc_defines = custom_target('Soc_defines',
input : './include/Soc.defines',
output : 'Soc.defines',
command : [cat , '@INPUT@'],
capture : true)

csr_defines = custom_target('csr_defines',
input : './include/csr.defines',
output : 'csr.defines',
command : [cat , '@INPUT@'],
capture : true)

Semi_FIFOF_bsv = custom_target('Semi_FIFOF_bsv',
input : './include/Semi_FIFOF.bsv',
output : 'Semi_FIFOF.bsv',
command : [cat , '@INPUT@'],
capture : true)

DMA_defines = custom_target('DMA_defines',
input : './include/DMA.defines',
output : 'DMA.defines',
command : [cat , '@INPUT@'],
capture : true)

gpio_defines = custom_target('gpio_defines',
input : './include/gpio.defines',
output : 'gpio.defines',
command : [cat , '@INPUT@'],
capture : true)

Logger_bsv = custom_target('Logger_bsv',
input : './include/Logger.bsv',
output : 'Logger.bsv',
command : [cat , '@INPUT@'],
capture : true)

jtagdefines_bsv = custom_target('jtagdefines_bsv',
input : './include/jtagdefines.bsv',
output : 'jtagdefines.bsv',
command : [cat , '@INPUT@'],
capture : true)

nand_defines = custom_target('nand_defines',
input : './include/nand.defines',
output : 'nand.defines',
command : [cat , '@INPUT@'],
capture : true)

fpu_defines = custom_target('fpu_defines',
input : './include/fpu.defines',
output : 'fpu.defines',
command : [cat , '@INPUT@'],
capture : true)

gen_py = custom_target('gen_py',
input : './include/gen.py',
output : 'gen.py',
command : [cat , '@INPUT@'],
capture : true)

csrgrp_defines = custom_target('csrgrp_defines',
input : './include/csrgrp.defines',
output : 'csrgrp.defines',
command : [cat , '@INPUT@'],
capture : true)

cache_defines = custom_target('cache_defines',
input : './include/cache.defines',
output : 'cache.defines',
command : [cat , '@INPUT@'],
capture : true)

includes = [sdram_defines, common_params_bsv, uart_defines, pwm_defines, plic_defines, log_txt, clint_defines, qspi_defines, Soc_defines, csr_defines, Semi_FIFOF_bsv, DMA_defines, gpio_defines, Logger_bsv, jtagdefines_bsv, nand_defines, fpu_defines, gen_py, csrgrp_defines, cache_defines]

device_common = custom_target('device_common',
input : './bsv/device_common.bsv',
output : 'device_common.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

RS232_modified = custom_target('RS232_modified',
input : './bsv/RS232_modified.bsv',
output : 'RS232_modified.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

replacement_dcache = custom_target('replacement_dcache',
input : './bsv/replacement_dcache.bsv',
output : 'replacement_dcache.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

ecc_hamming = custom_target('ecc_hamming',
input : './bsv/ecc_hamming.bsv',
output : 'ecc_hamming.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

replacement = custom_target('replacement',
input : './bsv/replacement.bsv',
output : 'replacement.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

bram_1r1w = custom_target('bram_1r1w',
input : './bsv/bram_1r1w.bsv',
output : 'bram_1r1w.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

bram_1rw = custom_target('bram_1rw',
input : './bsv/bram_1rw.bsv',
output : 'bram_1rw.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

io_func = custom_target('io_func',
input : './bsv/io_func.bsv',
output : 'io_func.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

cache_types = custom_target('cache_types',
input : './bsv/cache_types.bsv',
output : 'cache_types.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

ConcatReg = custom_target('ConcatReg',
input : './bsv/ConcatReg.bsv',
output : 'ConcatReg.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

CustomFIFOs = custom_target('CustomFIFOs',
input : './bsv/CustomFIFOs.bsv',
output : 'CustomFIFOs.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

integer_divider = custom_target('integer_divider',
input : './bsv/integer_divider.bsv',
output : 'integer_divider.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

signedmul = custom_target('signedmul',
input : './bsv/signedmul.bsv',
output : 'signedmul.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

decompress = custom_target('decompress',
input : './bsv/decompress.bsv',
output : 'decompress.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

stack = custom_target('stack',
input : './bsv/stack.bsv',
output : 'stack.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

globals = custom_target('globals',
input : './bsv/globals.bsv',
output : 'globals.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

common_types = custom_target('common_types',
input : './bsv/common_types.bsv',
output : 'common_types.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

TxRx = custom_target('TxRx',
input : './bsv/TxRx.bsv',
output : 'TxRx.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

Cur_Cycle = custom_target('Cur_Cycle',
input : './bsv/Cur_Cycle.bsv',
output : 'Cur_Cycle.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

Semi_FIFOF = custom_target('Semi_FIFOF',
input : './bsv/Semi_FIFOF.bsv',
output : 'Semi_FIFOF.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [  ] + includes)

jtagdtm = custom_target('jtagdtm',
input : './bsv/jtagdtm.bsv',
output : 'jtagdtm.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ ConcatReg ] + includes)

fa_dtlb = custom_target('fa_dtlb',
input : './bsv/fa_dtlb.bsv',
output : 'fa_dtlb.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ cache_types ] + includes,
depend_files : ['./include/cache.defines'])

fa_itlb = custom_target('fa_itlb',
input : './bsv/fa_itlb.bsv',
output : 'fa_itlb.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ cache_types ] + includes)

csr_grp1 = custom_target('csr_grp1',
input : './bsv/csr_grp1.bsv',
output : 'csr_grp1.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types ] + includes)

fwding = custom_target('fwding',
input : './bsv/fwding.bsv',
output : 'fwding.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types ] + includes)

fpu_fclass = custom_target('fpu_fclass',
input : './bsv/fpu_fclass.bsv',
output : 'fpu_fclass.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types ] + includes)

fpu_convert_sp_dp = custom_target('fpu_convert_sp_dp',
input : './bsv/fpu_convert_sp_dp.bsv',
output : 'fpu_convert_sp_dp.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types ] + includes)

fpu_fm_add_sub = custom_target('fpu_fm_add_sub',
input : './bsv/fpu_fm_add_sub.bsv',
output : 'fpu_fm_add_sub.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types ] + includes)

fpu_int_to_dp = custom_target('fpu_int_to_dp',
input : './bsv/fpu_int_to_dp.bsv',
output : 'fpu_int_to_dp.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types ] + includes)

fpu_dp_to_int = custom_target('fpu_dp_to_int',
input : './bsv/fpu_dp_to_int.bsv',
output : 'fpu_dp_to_int.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types ] + includes)

fpu_sp_to_int = custom_target('fpu_sp_to_int',
input : './bsv/fpu_sp_to_int.bsv',
output : 'fpu_sp_to_int.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types ] + includes)

fpu_sqrt = custom_target('fpu_sqrt',
input : './bsv/fpu_sqrt.bsv',
output : 'fpu_sqrt.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types ] + includes)

fpu_sign_injection = custom_target('fpu_sign_injection',
input : './bsv/fpu_sign_injection.bsv',
output : 'fpu_sign_injection.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types ] + includes)

fpu_int_to_sp = custom_target('fpu_int_to_sp',
input : './bsv/fpu_int_to_sp.bsv',
output : 'fpu_int_to_sp.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types ] + includes)

fpu_compare_min_max = custom_target('fpu_compare_min_max',
input : './bsv/fpu_compare_min_max.bsv',
output : 'fpu_compare_min_max.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types ] + includes)

restoring_div = custom_target('restoring_div',
input : './bsv/restoring_div.bsv',
output : 'restoring_div.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types ] + includes)

decoder = custom_target('decoder',
input : './bsv/decoder.bsv',
output : 'decoder.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types ] + includes)

AXI4_Lite_Types = custom_target('AXI4_Lite_Types',
input : './bsv/AXI4_Lite_Types.bsv',
output : 'AXI4_Lite_Types.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ Semi_FIFOF ] + includes)

AXI4_Types = custom_target('AXI4_Types',
input : './bsv/AXI4_Types.bsv',
output : 'AXI4_Types.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ Semi_FIFOF ] + includes)

ptwalk_rv32 = custom_target('ptwalk_rv32',
input : './bsv/ptwalk_rv32.bsv',
output : 'ptwalk_rv32.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ cache_types, globals ] + includes)

ptwalk_rv64 = custom_target('ptwalk_rv64',
input : './bsv/ptwalk_rv64.bsv',
output : 'ptwalk_rv64.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ cache_types, globals ] + includes)

null_dcache = custom_target('null_dcache',
input : './bsv/null_dcache.bsv',
output : 'null_dcache.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ cache_types, globals ] + includes)

null_icache = custom_target('null_icache',
input : './bsv/null_icache.bsv',
output : 'null_icache.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ globals, cache_types ] + includes)

mem_config = custom_target('mem_config',
input : './bsv/mem_config.bsv',
output : 'mem_config.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ bram_1rw, bram_1r1w ] + includes)

csr_grp7 = custom_target('csr_grp7',
input : './bsv/csr_grp7.bsv',
output : 'csr_grp7.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ ConcatReg, common_types ] + includes)

csr_grp6 = custom_target('csr_grp6',
input : './bsv/csr_grp6.bsv',
output : 'csr_grp6.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ ConcatReg, common_types ] + includes)

csr_grp5 = custom_target('csr_grp5',
input : './bsv/csr_grp5.bsv',
output : 'csr_grp5.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ ConcatReg, common_types ] + includes)

csr_grp4 = custom_target('csr_grp4',
input : './bsv/csr_grp4.bsv',
output : 'csr_grp4.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ ConcatReg, common_types ] + includes)

csr_grp3 = custom_target('csr_grp3',
input : './bsv/csr_grp3.bsv',
output : 'csr_grp3.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ ConcatReg, common_types ] + includes)

csr_grp2 = custom_target('csr_grp2',
input : './bsv/csr_grp2.bsv',
output : 'csr_grp2.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ ConcatReg, common_types ] + includes)

fpu_divider = custom_target('fpu_divider',
input : './bsv/fpu_divider.bsv',
output : 'fpu_divider.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types, integer_divider ] + includes)

combo = custom_target('combo',
input : './bsv/combo.bsv',
output : 'combo.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ signedmul, common_types ] + includes)

debug_types = custom_target('debug_types',
input : './bsv/debug_types.bsv',
output : 'debug_types.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ AXI4_Types, AXI4_Lite_Types ] + includes)

registerfile = custom_target('registerfile',
input : './bsv/registerfile.bsv',
output : 'registerfile.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types, debug_types ] + includes)

gshare_fa = custom_target('gshare_fa',
input : './bsv/gshare_fa.bsv',
output : 'gshare_fa.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types, stack ] + includes)

AXI4_Lite_Fabric = custom_target('AXI4_Lite_Fabric',
input : './bsv/AXI4_Lite_Fabric.bsv',
output : 'AXI4_Lite_Fabric.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ Cur_Cycle, Semi_FIFOF, AXI4_Lite_Types ] + includes)

mbox = custom_target('mbox',
input : './bsv/mbox.bsv',
output : 'mbox.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types, combo, restoring_div ] + includes)

fpu = custom_target('fpu',
input : './bsv/fpu.bsv',
output : 'fpu.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types, fpu_compare_min_max, fpu_int_to_sp, fpu_sign_injection, fpu_divider, fpu_sqrt, fpu_sp_to_int, fpu_dp_to_int, fpu_int_to_dp, fpu_fm_add_sub, fpu_convert_sp_dp, fpu_fclass ] + includes)

alu = custom_target('alu',
input : './bsv/alu.bsv',
output : 'alu.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ mbox, fpu, common_types ] + includes)

stage1 = custom_target('stage1',
input : './bsv/stage1.bsv',
output : 'stage1.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types, globals, decompress ] + includes)

AXI4_Fabric = custom_target('AXI4_Fabric',
input : './bsv/AXI4_Fabric.bsv',
output : 'AXI4_Fabric.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ Cur_Cycle, Semi_FIFOF, AXI4_Types ] + includes)

sign_dump = custom_target('sign_dump',
input : './bsv/sign_dump.bsv',
output : 'sign_dump.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types, AXI4_Types, AXI4_Fabric, Semi_FIFOF ] + includes)

clint = custom_target('clint',
input : './bsv/clint.bsv',
output : 'clint.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ Semi_FIFOF, AXI4_Lite_Types, AXI4_Types, device_common ] + includes)

csr_daisy = custom_target('csr_daisy',
input : './bsv/csr_daisy.bsv',
output : 'csr_daisy.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types, ConcatReg, csr_grp1, csr_grp2, csr_grp3, csr_grp4, csr_grp5, csr_grp6, csr_grp7 ] + includes)

csr = custom_target('csr',
input : './bsv/csr.bsv',
output : 'csr.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ common_types, ConcatReg, csr_daisy, debug_types ] + includes)

stage5 = custom_target('stage5',
input : './bsv/stage5.bsv',
output : 'stage5.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ TxRx, common_types, csr, debug_types ] + includes)

stage4 = custom_target('stage4',
input : './bsv/stage4.bsv',
output : 'stage4.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ CustomFIFOs, TxRx, common_types, globals ] + includes)

stage0 = custom_target('stage0',
input : './bsv/stage0.bsv',
output : 'stage0.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ TxRx, common_types, globals, gshare_fa ] + includes)

debug_halt_loop = custom_target('debug_halt_loop',
input : './bsv/debug_halt_loop.bsv',
output : 'debug_halt_loop.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ AXI4_Types, AXI4_Fabric, AXI4_Lite_Types, AXI4_Lite_Fabric, Semi_FIFOF ] + includes)

riscvDebug013 = custom_target('riscvDebug013',
input : './bsv/riscvDebug013.bsv',
output : 'riscvDebug013.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ Semi_FIFOF, AXI4_Types, AXI4_Lite_Types, ConcatReg, debug_types ] + includes)

err_slave = custom_target('err_slave',
input : './bsv/err_slave.bsv',
output : 'err_slave.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ AXI4_Types, AXI4_Fabric, AXI4_Lite_Types, AXI4_Lite_Fabric, Semi_FIFOF ] + includes)

l1dcache = custom_target('l1dcache',
input : './bsv/l1dcache.bsv',
output : 'l1dcache.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ cache_types, globals, mem_config, replacement_dcache, ecc_hamming ] + includes)

l1dcache_vipt = custom_target('l1dcache_vipt',
input : './bsv/l1dcache_vipt.bsv',
output : 'l1dcache_vipt.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ cache_types, globals, mem_config, replacement_dcache, ecc_hamming ] + includes)

l1icache = custom_target('l1icache',
input : './bsv/l1icache.bsv',
output : 'l1icache.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ globals, cache_types, mem_config, replacement, ecc_hamming ] + includes)

l1icache_vipt = custom_target('l1icache_vipt',
input : './bsv/l1icache_vipt.bsv',
output : 'l1icache_vipt.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ globals, cache_types, mem_config, replacement, ecc_hamming ] + includes)

stage3 = custom_target('stage3',
input : './bsv/stage3.bsv',
output : 'stage3.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ TxRx, alu, fwding, common_types, globals ] + includes)

bootrom = custom_target('bootrom',
input : './bsv/bootrom.bsv',
output : 'bootrom.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ Semi_FIFOF, AXI4_Types, AXI4_Fabric, AXI4_Lite_Types, AXI4_Lite_Fabric, device_common ] + includes)

bram = custom_target('bram',
input : './bsv/bram.bsv',
output : 'bram.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ Semi_FIFOF, AXI4_Types, AXI4_Fabric, AXI4_Lite_Types, AXI4_Lite_Fabric, device_common ] + includes)

stage2 = custom_target('stage2',
input : './bsv/stage2.bsv',
output : 'stage2.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ TxRx, registerfile, decoder, common_types, globals, debug_types ] + includes)

uart = custom_target('uart',
input : './bsv/uart.bsv',
output : 'uart.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ AXI4_Lite_Types, AXI4_Lite_Fabric, AXI4_Types, AXI4_Fabric, Semi_FIFOF, RS232_modified, device_common ] + includes)

dmem = custom_target('dmem',
input : './bsv/dmem.bsv',
output : 'dmem.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ cache_types, globals, io_func, l1dcache_vipt, l1dcache, null_dcache, fa_dtlb ] + includes)

imem = custom_target('imem',
input : './bsv/imem.bsv',
output : 'imem.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ globals, cache_types, io_func, fa_itlb, l1icache_vipt, l1icache, null_icache ] + includes)


riscv = custom_target('riscv',
input : './bsv/riscv.bsv',
output : 'riscv.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ TxRx, stage0, stage1, stage2, stage3, stage4, stage5, common_types, CustomFIFOs, globals, debug_types ] + includes)

cclass = custom_target('cclass',
input : './bsv/cclass.bsv',
output : 'cclass.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ Semi_FIFOF, AXI4_Types, AXI4_Fabric, riscv, common_types, globals, cache_types, imem, dmem, ptwalk_rv64, ptwalk_rv32, debug_types ] + includes)

Soc = custom_target('Soc',
input : './bsv/Soc.bsv',
output : 'Soc.bo',
command : [bsc] + options + ['@INPUT@'],
depends : [ Semi_FIFOF, AXI4_Types, AXI4_Fabric, cclass, common_types, uart, clint, sign_dump, err_slave, debug_types, jtagdtm, riscvDebug013, debug_halt_loop ] + includes)

TbSoc = custom_target('TbSoc',
input : './bsv/TbSoc.bsv',
output : 'TbSoc.bo',
command : [bsc, '-g', 'mkTbSoc'] + options + ['@INPUT@'],
depends : [ Soc, Semi_FIFOF, AXI4_Types, AXI4_Fabric, uart, common_types, device_common, bram, bootrom ] + includes,
build_by_default : true)

