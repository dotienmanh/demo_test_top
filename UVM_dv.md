# Hướng dẫn chạy dv cho core ibex
## Cách 1: Chạy thủ công từng bước 1 (Thuận tiện cho debug)
> Nhớ `source .bashrc` để lấy các path cần thiết
### Step1: Đọc và tải các tool cần thiết cho chạy dv
> Truy cập `https://github.com/lowRISC/ibex/tree/master/dv/uvm/core_ibex`

### Step2: Chạy makefile
- Chạy make, thay `$TEST_NAME` bằng các test name trong file sau `https://ibex.reports.lowrisc.org/opentitan/latest/report.html`. Nếu muốn chạy tất cả các test thì bỏ option `TEST` đi
```
make clean && make --keep-going IBEX_CONFIG=opentitan SIMULATOR=xlm ISS=spike ITERATIONS=1 SEED=1 TEST=$TEST_NAME WAVES=0 COV=0
```
### Step3: Sau khi chạy sẽ thấy lệnh xrun đầu đang gen sai rpath. Chạy lại lệnh sau:
> Lệnh được chạy trên `usr18`, các usr khác chỉnh lại đúng path của `ibex_repo_base` 
```
xrun -64bit -q -f /home/usr18/ibex/dv/uvm/core_ibex/ibex_dv.f -sv -licqueue -uvm -uvmhome CDNS-1.2 -define UVM_REGEX_NO_DPI -elaborate -l /home/usr18/ibex/dv/uvm/core_ibex/out/build/tb/compile_tb.log -xmlibdirpath /home/usr18/ibex/dv/uvm/core_ibex/out/build/tb -access rw -defparam core_ibex_tb_top.RV32E=0 -define IBEX_CFG_RV32M=ibex_pkg::RV32MSingleCycle -define IBEX_CFG_RV32B=ibex_pkg::RV32BOTEarlGrey -define IBEX_CFG_RegFile=ibex_pkg::RegFileFF -defparam core_ibex_tb_top.BranchTargetALU=1 -defparam core_ibex_tb_top.WritebackStage=1 -defparam core_ibex_tb_top.ICache=1 -defparam core_ibex_tb_top.ICacheECC=1 -defparam core_ibex_tb_top.ICacheScramble=1 -defparam core_ibex_tb_top.BranchPredictor=0 -defparam core_ibex_tb_top.DbgTriggerEn=1 -defparam core_ibex_tb_top.SecureIbex=1 -defparam core_ibex_tb_top.PMPEnable=1 -defparam core_ibex_tb_top.PMPGranularity=0 -defparam core_ibex_tb_top.PMPNumRegions=16 -defparam core_ibex_tb_top.MHPMCounterNum=10 -defparam core_ibex_tb_top.MHPMCounterWidth=32 -f ibex_dv_cosim_dpi.f -I/home/usr18/ibex/dv/cosim -lriscv -lsoftfloat -ldl -ldisasm -lfdt -lfesvr -L/lib -L//lib -I/include -I/include/softfloat -I//include '-Wld,-Xlinker,-rpath,-Xlinker,/lib' -lstdc++
```
- Nếu ở dòng cuối cùng gen ra không có *E tức là không có lỗi thì chạy tiếp, còn không tìm lỗi và debug
### Step4: Chạy lại make file như trên, nhưng **nhớ bỏ `make clean`** và thay `$TEST_NAME`:
```
make --keep-going IBEX_CONFIG=opentitan SIMULATOR=xlm ISS=spike ITERATIONS=1 SEED=1 TEST=$TEST_NAME WAVES=0 COV=0
```
- Sau khi chạy, file trace_core_000000.log và các file log khác sẽ nằm ở path
```
/home/usr9/ibex/ibex_test/ibex/dv/uvm/core_ibex/out/run/tests/riscv_arithmetic_basic_test.1
```
- Nếu vẫn báo không thấy file *trace_core_000000.log* đâu thì xem log terminal có thông báo như sau không
![image](https://github.com/user-attachments/assets/08ed5123-19f3-47f6-9ac2-84993b595d1e)
- Nếu có, hãy coppy lệnh đó và chạy lại để debug lỗi
```
xrun -64bit -R -xmlibdirpath /home/usr9/ibex/ibex_test/ibex/dv/uvm/core_ibex/out/build/tb -licqueue -svseed 1 -svrnc rand_struct -nokey -l /home/usr9/ibex/ibex_test/ibex/dv/uvm/core_ibex/out/run/tests/riscv_arithmetic_basic_test.1/rtl_sim.log +UVM_MAX_QUIT_COUNT=5 +UVM_TESTNAME=core_ibex_base_test +UVM_VERBOSITY=UVM_LOW +bin=/home/usr9/ibex/ibex_test/ibex/dv/uvm/core_ibex/out/run/tests/riscv_arithmetic_basic_test.1/test.bin +ibex_tracer_file_base=/home/usr9/ibex/ibex_test/ibex/dv/uvm/core_ibex/out/run/tests/riscv_arithmetic_basic_test.1/trace_core +cosim_log_file=/home/usr9/ibex/ibex_test/ibex/dv/uvm/core_ibex/out/run/tests/riscv_arithmetic_basic_test.1/spike_cosim_trace_core_00000000.log -input '@database -open /home/usr9/ibex/ibex_test/ibex/dv/uvm/core_ibex/out/run/tests/riscv_arithmetic_basic_test.1/waves -shm -default' -input '@probe -create core_ibex_tb_top -all -memories -depth all' -input @run +signature_addr=8ffffffc +test_timeout_s=1800
```
- Còn nếu không thấy báo lỗi như vậy, có thể do tín hiệu rvalid từ core gửi ra sai, hoặc vấn đề gì đó, hãy tới path sau và tìm lỗi trong các file log
```
/home/usr9/ibex/ibex_test/ibex/dv/uvm/core_ibex/out/run/tests/riscv_arithmetic_basic_test.1
```

## Cách 2: Chạy bằng script (Nếu bạn đang lười, chạy compile các kiểu đúng hết rồi không phải debug và không muốn ngồi canh lệnh)
> Vẫn nhớ `source .bashrc` để lấy các path cần thiết
- Tại home
```
source .bashrc
cd $IBEX_BASE_REPO/dv/uvm/core_ibex
./run_dv.sh
```
> GLHF
