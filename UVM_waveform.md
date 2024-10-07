# Cách bật waveform sau khi chạy uvm
## Step1: Chạy make cho uvm nhưng thay option *WAVES=1*
```
make clean && make --keep-going IBEX_CONFIG=opentitan SIMULATOR=xlm ISS=spike ITERATIONS=1 SEED=1 TEST=riscv_arithmetic_basic_test WAVES=1 COV=0
```
- Hoặc đơn giản hãy chạy script theo cách 2 của doc cho dv `https://github.com/dotienmanh/thietkeso_cuoi_ki/blob/main/ibex_dv_manual.md`
## Step2: Mở wave
- Vào folder chứa file log
```
cd /home/usr9/ibex/ibex_test/ibex/dv/uvm/core_ibex/out/run/tests/riscv_arithmetic_basic_test.1/waves.shm
```
- Mở gui lên
```
simvision
```
- Trong gui, import database vào bằng các thao tác sau
![image](https://github.com/user-attachments/assets/93644cb5-abcf-4de6-b2c1-99d36454cf96)
> Chọn định dạng file
![image](https://github.com/user-attachments/assets/29be671e-39aa-4a21-a86d-94fb546ca248)
> Chọn file .trn và open
![image](https://github.com/user-attachments/assets/bffab35d-9489-4f64-94c3-20e8c0ac7356)
> Thao tác với gui
![Screenshot 2024-10-06 165721](https://github.com/user-attachments/assets/e65fcbb8-aaa7-4260-be5e-4ad1f57d0d74)
>
> DONE
