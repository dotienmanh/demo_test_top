`ifdef RISCV_FORMAL
  `define RVFI
`endif

// `include "prim_assert.sv"
// `include "dv_fcov_macros.svh"

/**
 * Top level module of the ibex RISC-V core
 */

module riscv_core import ibex_pkg::*; #(
  parameter bit                     PMPEnable        = 1'b0,
  parameter int unsigned            PMPGranularity   = 0,
  parameter int unsigned            PMPNumRegions    = 4,
  parameter ibex_pkg::pmp_cfg_t     PMPRstCfg[16]    = ibex_pkg::PmpCfgRst,
  parameter logic [33:0]            PMPRstAddr[16]   = ibex_pkg::PmpAddrRst,
  parameter ibex_pkg::pmp_mseccfg_t PMPRstMsecCfg    = ibex_pkg::PmpMseccfgRst,
  parameter int unsigned            MHPMCounterNum   = 0,
  parameter int unsigned            MHPMCounterWidth = 40,
  parameter bit                     RV32E            = 1'b0,
  parameter rv32m_e                 RV32M            = RV32MFast,
  parameter rv32b_e                 RV32B            = RV32BNone,
  parameter bit                     BranchTargetALU  = 1'b0,
  parameter bit                     WritebackStage   = 1'b0,
  parameter bit                     ICache           = 1'b0,
  parameter bit                     ICacheECC        = 1'b0,
  parameter int unsigned            BusSizeECC       = BUS_SIZE,
  parameter int unsigned            TagSizeECC       = IC_TAG_SIZE,
  parameter int unsigned            LineSizeECC      = IC_LINE_SIZE,
  parameter bit                     BranchPredictor  = 1'b0,
  parameter bit                     DbgTriggerEn     = 1'b0,
  parameter int unsigned            DbgHwBreakNum    = 1,
  parameter bit                     ResetAll         = 1'b0,
  parameter lfsr_seed_t             RndCnstLfsrSeed  = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t             RndCnstLfsrPerm  = RndCnstLfsrPermDefault,
  parameter bit                     SecureIbex       = 1'b0,
  parameter bit                     DummyInstructions= 1'b0,
  parameter bit                     RegFileECC       = 1'b0,
  parameter int unsigned            RegFileDataWidth = 32,
  parameter bit                     MemECC           = 1'b0,
  parameter int unsigned            MemDataWidth     = MemECC ? 32 + 7 : 32,
  parameter int unsigned            DmHaltAddr       = 32'h1A110800,
  parameter int unsigned            DmExceptionAddr  = 32'h1A110808
)(
  // Clock and Reset
  input  logic                         clk_i,
  input  logic                         rst_ni,
  input  logic [31:0]                  hart_id_i,
  input  logic [31:0]                  boot_addr_i,

  // Instruction memory interface
  output logic                         instr_req_o,
  input  logic                         instr_gnt_i,
  input  logic                         instr_rvalid_i,
  output logic [31:0]                  instr_addr_o,
  input  logic [MemDataWidth-1:0]      instr_rdata_i,
  input  logic                         instr_err_i,

  // Data memory interface
  output logic                         data_req_o,
  input  logic                         data_gnt_i,
  input  logic                         data_rvalid_i,
  output logic                         data_we_o,
  output logic [3:0]                   data_be_o,
  output logic [31:0]                  data_addr_o,
  output logic [MemDataWidth-1:0]      data_wdata_o,
  input  logic [MemDataWidth-1:0]      data_rdata_i,
  input  logic                         data_err_i,

  // Register file interface
  output logic                         dummy_instr_id_o,
  output logic                         dummy_instr_wb_o,
  output logic [4:0]                   rf_raddr_a_o,
  output logic [4:0]                   rf_raddr_b_o,
  output logic [4:0]                   rf_waddr_wb_o,
  output logic                         rf_we_wb_o,
  output logic [RegFileDataWidth-1:0]  rf_wdata_wb_ecc_o,
  input  logic [RegFileDataWidth-1:0]  rf_rdata_a_ecc_i,
  input  logic [RegFileDataWidth-1:0]  rf_rdata_b_ecc_i,

  // RAMs interface
  output logic [IC_NUM_WAYS-1:0]       ic_tag_req_o,
  output logic                         ic_tag_write_o,
  output logic [IC_INDEX_W-1:0]        ic_tag_addr_o,
  output logic [TagSizeECC-1:0]        ic_tag_wdata_o,
  input  logic [TagSizeECC-1:0]        ic_tag_rdata_i [IC_NUM_WAYS],
  output logic [IC_NUM_WAYS-1:0]       ic_data_req_o,
  output logic                         ic_data_write_o,
  output logic [IC_INDEX_W-1:0]        ic_data_addr_o,
  output logic [LineSizeECC-1:0]       ic_data_wdata_o,
  input  logic [LineSizeECC-1:0]       ic_data_rdata_i [IC_NUM_WAYS],
  input  logic                         ic_scr_key_valid_i,
  output logic                         ic_scr_key_req_o,

  // Interrupt inputs
  input  logic                         irq_software_i,
  input  logic                         irq_timer_i,
  input  logic                         irq_external_i,
  input  logic [14:0]                  irq_fast_i,
  input  logic                         irq_nm_i,       // non-maskeable interrupt
  output logic                         irq_pending_o,

  // Debug Interface
  input  logic                         debug_req_i,
  output crash_dump_t                  crash_dump_o,
  // SEC_CM: EXCEPTION.CTRL_FLOW.LOCAL_ESC
  // SEC_CM: EXCEPTION.CTRL_FLOW.GLOBAL_ESC
  output logic                         double_fault_seen_o,

  // RISC-V Formal Interface
  // Does not comply with the coding standards of _i/_o suffixes, but follows
  // the convention of RISC-V Formal Interface Specification.
`ifdef RVFI
  output logic                         rvfi_valid,
  output logic [63:0]                  rvfi_order,
  output logic [31:0]                  rvfi_insn,
  output logic                         rvfi_trap,
  output logic                         rvfi_halt,
  output logic                         rvfi_intr,
  output logic [ 1:0]                  rvfi_mode,
  output logic [ 1:0]                  rvfi_ixl,
  output logic [ 4:0]                  rvfi_rs1_addr,
  output logic [ 4:0]                  rvfi_rs2_addr,
  output logic [ 4:0]                  rvfi_rs3_addr,
  output logic [31:0]                  rvfi_rs1_rdata,
  output logic [31:0]                  rvfi_rs2_rdata,
  output logic [31:0]                  rvfi_rs3_rdata,
  output logic [ 4:0]                  rvfi_rd_addr,
  output logic [31:0]                  rvfi_rd_wdata,
  output logic [31:0]                  rvfi_pc_rdata,
  output logic [31:0]                  rvfi_pc_wdata,
  output logic [31:0]                  rvfi_mem_addr,
  output logic [ 3:0]                  rvfi_mem_rmask,
  output logic [ 3:0]                  rvfi_mem_wmask,
  output logic [31:0]                  rvfi_mem_rdata,
  output logic [31:0]                  rvfi_mem_wdata,
  output logic [31:0]                  rvfi_ext_pre_mip,
  output logic [31:0]                  rvfi_ext_post_mip,
  output logic                         rvfi_ext_nmi,
  output logic                         rvfi_ext_nmi_int,
  output logic                         rvfi_ext_debug_req,
  output logic                         rvfi_ext_debug_mode,
  output logic                         rvfi_ext_rf_wr_suppress,
  output logic [63:0]                  rvfi_ext_mcycle,
  output logic [31:0]                  rvfi_ext_mhpmcounters [10],
  output logic [31:0]                  rvfi_ext_mhpmcountersh [10],
  output logic                         rvfi_ext_ic_scr_key_valid,
  output logic                         rvfi_ext_irq_valid,
  `endif

  // CPU Control Signals
  // SEC_CM: FETCH.CTRL.LC_GATED
  input  ibex_mubi_t                   fetch_enable_i,
  output logic                         alert_minor_o,
  output logic                         alert_major_internal_o,
  output logic                         alert_major_bus_o,
  output ibex_mubi_t                   core_busy_o
);

  //////////////////////
  // Clock management //
  //////////////////////

  localparam int unsigned PMPNumChan      = 3;
  // SEC_CM: CORE.DATA_REG_SW.SCA
  localparam bit          DataIndTiming     = SecureIbex;
  localparam bit          PCIncrCheck       = SecureIbex;
  localparam bit          ShadowCSR         = 1'b0;

  //////////////////////
  //   Signals List   //
  //////////////////////

  // IF/ID signals
  logic        dummy_instr_id;
  logic        instr_valid_id;
  logic        instr_new_id;
  logic [31:0] instr_rdata_id;                 // Instruction sampled inside IF stage
  logic [31:0] instr_rdata_alu_id;             // Instruction sampled inside IF stage (replicated to
                                               // ease fan-out)
  logic [15:0] instr_rdata_c_id;               // Compressed instruction sampled inside IF stage
  logic        instr_is_compressed_id;
  logic        instr_perf_count_id;
  logic        instr_bp_taken_id;
  logic        instr_fetch_err;                // Bus error on instr fetch
  logic        instr_fetch_err_plus2;          // Instruction error is misaligned
  logic        illegal_c_insn_id;              // Illegal compressed instruction sent to ID stage
  logic [31:0] pc_if;                          // Program counter in IF stage
  logic [31:0] pc_id;                          // Program counter in ID stage
  logic [31:0] pc_wb;                          // Program counter in WB stage
  logic [33:0] imd_val_d_ex[2];                // Intermediate register for multicycle Ops
  logic [33:0] imd_val_q_ex[2];                // Intermediate register for multicycle Ops
  logic [1:0]  imd_val_we_ex;

  logic        data_ind_timing;
  logic        dummy_instr_en;
  logic [2:0]  dummy_instr_mask;
  logic        dummy_instr_seed_en;
  logic [31:0] dummy_instr_seed;
  logic        icache_enable;
  logic        icache_inval;
  logic        icache_ecc_error;
  logic        pc_mismatch_alert;
  logic        csr_shadow_err;

  logic        instr_first_cycle_id;
  logic        instr_valid_clear;
  logic        pc_set;
  logic        nt_branch_mispredict;
  logic [31:0] nt_branch_addr;
  pc_sel_e     pc_mux_id;                      // Mux selector for next PC
  exc_pc_sel_e exc_pc_mux_id;                  // Mux selector for exception PC
  exc_cause_t  exc_cause;                      // Exception cause

  logic        instr_intg_err;
  logic        lsu_load_err, lsu_load_err_raw;
  logic        lsu_store_err, lsu_store_err_raw;
  logic        lsu_load_resp_intg_err;
  logic        lsu_store_resp_intg_err;

  logic        expecting_load_resp_id;
  logic        expecting_store_resp_id;

  // LSU signals
  logic        lsu_addr_incr_req;
  logic [31:0] lsu_addr_last;

  // Jump and branch target and decision (EX->IF)
  logic [31:0] branch_target_ex;
  logic        branch_decision;

  // Core busy signals
  logic        ctrl_busy;
  logic        if_busy;
  logic        lsu_busy;

  // Register File
  logic [4:0]  rf_raddr_a;
  logic [31:0] rf_rdata_a;
  logic [4:0]  rf_raddr_b;
  logic [31:0] rf_rdata_b;
  logic        rf_ren_a;
  logic        rf_ren_b;
  logic [4:0]  rf_waddr_wb;
  logic [31:0] rf_wdata_wb;
  // Writeback register write data that can be used on the forwarding path (doesn't factor in memory
  // read data as this is too late for the forwarding path)
  logic [31:0] rf_wdata_fwd_wb;
  logic [31:0] rf_wdata_lsu;
  logic        rf_we_wb;
  logic        rf_we_lsu;
  logic        rf_ecc_err_comb;

  logic [4:0]  rf_waddr_id;
  logic [31:0] rf_wdata_id;
  logic        rf_we_id;
  logic        rf_rd_a_wb_match;
  logic        rf_rd_b_wb_match;

  // ALU Control
  alu_op_e     alu_operator_ex;
  logic [31:0] alu_operand_a_ex;
  logic [31:0] alu_operand_b_ex;

  logic [31:0] bt_a_operand;
  logic [31:0] bt_b_operand;

  logic [31:0] alu_adder_result_ex;    // Used to forward computed address to LSU
  logic [31:0] result_ex;

  // Multiplier Control
  logic        mult_en_ex;
  logic        div_en_ex;
  logic        mult_sel_ex;
  logic        div_sel_ex;
  md_op_e      multdiv_operator_ex;
  logic [1:0]  multdiv_signed_mode_ex;
  logic [31:0] multdiv_operand_a_ex;
  logic [31:0] multdiv_operand_b_ex;
  logic        multdiv_ready_id;

  // CSR control
  logic        csr_access;
  csr_op_e     csr_op;
  logic        csr_op_en;
  csr_num_e    csr_addr;
  logic [31:0] csr_rdata;
  logic [31:0] csr_wdata;
  logic        illegal_csr_insn_id;    // CSR access to non-existent register,
                                       // with wrong priviledge level,
                                       // or missing write permissions

  // Data Memory Control
  logic        lsu_we;
  logic [1:0]  lsu_type;
  logic        lsu_sign_ext;
  logic        lsu_req;
  logic        lsu_rdata_valid;
  logic [31:0] lsu_wdata;
  logic        lsu_req_done;

  // stall control
  logic        id_in_ready;
  logic        ex_valid;

  logic        lsu_resp_valid;
  logic        lsu_resp_err;

  // Signals between instruction core interface and pipe (if and id stages)
  logic        instr_req_int;          // Id stage asserts a req to instruction core interface
  logic        instr_req_gated;
  logic        instr_exec;

  // Writeback stage
  logic           en_wb;
  wb_instr_type_e instr_type_wb;
  logic           ready_wb;
  logic           rf_write_wb;
  logic           outstanding_load_wb;
  logic           outstanding_store_wb;
  logic           dummy_instr_wb;

  // Interrupts
  logic        nmi_mode;
  irqs_t       irqs;
  logic        csr_mstatus_mie;
  logic [31:0] csr_mepc, csr_depc;

  // PMP signals
  logic [33:0]  csr_pmp_addr [PMPNumRegions];
  pmp_cfg_t     csr_pmp_cfg  [PMPNumRegions];
  pmp_mseccfg_t csr_pmp_mseccfg;
  logic         pmp_req_err  [PMPNumChan];
  logic         data_req_out;

  logic        csr_save_if;
  logic        csr_save_id;
  logic        csr_save_wb;
  logic        csr_restore_mret_id;
  logic        csr_restore_dret_id;
  logic        csr_save_cause;
  logic        csr_mtvec_init;
  logic [31:0] csr_mtvec;
  logic [31:0] csr_mtval;
  logic        csr_mstatus_tw;
  priv_lvl_e   priv_mode_id;
  priv_lvl_e   priv_mode_lsu;

  // debug mode and dcsr configuration
  logic        debug_mode;
  logic        debug_mode_entering;
  dbg_cause_e  debug_cause;
  logic        debug_csr_save;
  logic        debug_single_step;
  logic        debug_ebreakm;
  logic        debug_ebreaku;
  logic        trigger_match;

  // signals relating to instruction movements between pipeline stages
  // used by performance counters and RVFI
  logic        instr_id_done;
  logic        instr_done_wb;

  logic        perf_instr_ret_wb;
  logic        perf_instr_ret_compressed_wb;
  logic        perf_instr_ret_wb_spec;
  logic        perf_instr_ret_compressed_wb_spec;
  logic        perf_iside_wait;
  logic        perf_dside_wait;
  logic        perf_mul_wait;
  logic        perf_div_wait;
  logic        perf_jump;
  logic        perf_branch;
  logic        perf_tbranch;
  logic        perf_load;
  logic        perf_store;

  // for RVFI
  logic        illegal_insn_id, unused_illegal_insn_id; // ID stage sees an illegal instruction

  // UPDATE
  // ID/Controller (nối giữa ID và controller)
  logic ebrk_insn;
  logic mret_insn;
  logic dret_insn;
  logic ecall_insn;
  logic wfi_insn;
  logic jump_set;

  // ID/EX (nối giữa ID và EX)
  logic [31:0] rf_rdata_a_ex;
  logic [31:0] rf_rdata_b_ex;
  
  logic ibex_pkg::rf_wd_sel_e rf_wdata_sel_ex;
  logic rf_we_ex;
  logic [4:0] rf_waddr_ex;

  logic imm_a_sel_e imm_a_mux_sel_ex;
  logic imm_b_sel_e imm_b_mux_sel_ex;

  logic [31:0] instr_ex;
  logic [4:0] instr_rs1_ex;
  logic [4:0] instr_rs2_ex;
  logic [4:0] instr_rs3_ex;
  logic [4:0] instr_rd_ex;
  logic [31:0] pc_ex;
  logic instr_is_compressed_ex;

  logic [31:0] imm_i_type_ex;
  logic [31:0] imm_b_type_ex;
  logic [31:0] imm_s_type_ex;
  logic [31:0] imm_j_type_ex;
  logic [31:0] imm_u_type_ex;
  logic [31:0] zimm_rs1_type_ex;

  logic op_a_sel_e         bt_a_mux_sel_EX;
  logic imm_b_sel_e        bt_b_mux_sel_EX;

  logic   alu_op_e         alu_operator_EX;
  logic   op_a_sel_e       alu_op_a_mux_sel_EX;
  logic   op_b_sel_e       alu_op_b_mux_sel_EX;
  logic                    alu_instr_first_cycle_i;

  logic [1:0]            imd_val_we_o;
  logic [33:0]           imd_val_d_o[2];
  logic [33:0]           imd_val_q_i[2];

  logic op_a_sel_e    alu_op_a_mux_sel_ex;
  logic op_a_sel_e    alu_op_b_mux_sel_EX;
  
  //////////////////////
  // Clock management //
  //////////////////////

  // Before going to sleep, wait for I- and D-side
  // interfaces to finish ongoing operations.
    // For non secure Ibex, synthesis is allowed to optimize core_busy_o.
    assign core_busy_o = (ctrl_busy || if_busy || lsu_busy) ? IbexMuBiOn : IbexMuBiOff;

  //////////////////////
  //     IF Stage     //
  //////////////////////

  IF_top #(
    .DmHaltAddr       (DmHaltAddr),
    .DmExceptionAddr  (DmExceptionAddr),
    .DummyInstructions(DummyInstructions),
    .ICache           (ICache),
    .ICacheECC        (ICacheECC),
    .BusSizeECC       (BusSizeECC),
    .TagSizeECC       (TagSizeECC),
    .LineSizeECC      (LineSizeECC),
    .PCIncrCheck      (PCIncrCheck),
    .ResetAll         (ResetAll),
    .RndCnstLfsrSeed  (RndCnstLfsrSeed),
    .RndCnstLfsrPerm  (RndCnstLfsrPerm),
    .BranchPredictor  (BranchPredictor),
    .MemECC           (MemECC),
    .MemDataWidth     (MemDataWidth)
  ) if_stage_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .boot_addr_i(boot_addr_i),      // CONNECTED input core
    .req_i      (instr_req_gated),  // CONNECTED  assign ở ngoài core vào instruction request control

    // instruction cache interface
    .instr_req_o       (instr_req_o),     // CONNECTED OUTPUT CORE
    .instr_addr_o      (instr_addr_o),    // CONNECTED OUTPUT CORE
    .instr_gnt_i       (instr_gnt_i),     // CONNECTED INPUT CORE
    .instr_rvalid_i    (instr_rvalid_i),  // CONNECTED INPUT CORE
    .instr_rdata_i     (instr_rdata_i),   // CONNECTED INPUT CORE
    .instr_bus_err_i   (instr_err_i),     // CONNECTED INPUT CORE
    .instr_intg_err_o  (instr_intg_err),  // CONNECTED (điều kiện cho alert_major_bus_o)

    // ICache RAM IO
    .ic_tag_req_o      (ic_tag_req_o),        // CONNECTED OUTPUT CORE
    .ic_tag_write_o    (ic_tag_write_o),      // CONNECTED OUTPUT CORE 
    .ic_tag_addr_o     (ic_tag_addr_o),       // CONNECTED OUTPUT CORE
    .ic_tag_wdata_o    (ic_tag_wdata_o),      // CONNECTED OUTPUT CORE
    .ic_tag_rdata_i    (ic_tag_rdata_i),      // CONNECTED INPUT CORE
    .ic_data_req_o     (ic_data_req_o),       // CONNECTED OUTPUT CORE
    .ic_data_write_o   (ic_data_write_o),     // CONNECTED OUTPUT CORE
    .ic_data_addr_o    (ic_data_addr_o),      // CONNECTED OUTPUT CORE
    .ic_data_wdata_o   (ic_data_wdata_o),     // CONNECTED OUTPUT CORE
    .ic_data_rdata_i   (ic_data_rdata_i),     // CONNECTED INPUT CORE
    .ic_scr_key_valid_i(ic_scr_key_valid_i),  // CONNECTED INPUT CORE
    .ic_scr_key_req_o  (ic_scr_key_req_o),    // NOT CONNECTED OUTPUT CORE (cần nối vào input cs_register)

    // control signals
    .instr_valid_clear_i   (instr_valid_clear),     // NOT CONNECTED (output từ controller)
    .pc_set_i              (pc_set),                // NOT CONNECTED (output từ controller)
    .pc_mux_i              (pc_mux_id),             // NOT CONNECTED (output từ controller)
    .nt_branch_mispredict_i(nt_branch_mispredict),  // NOT CONNECTED (output từ controller)

    .nt_branch_addr_i  (nt_branch_addr),     // NOT CONNECTED  (output từ controller)     // not taken branch address in ID/EX

    .exc_pc_mux_i          (exc_pc_mux_id),   // NOT CONNECTED  (output từ controller)
    .exc_cause             (exc_cause),       // NOT CONNECTED  (output từ controller)

    .dummy_instr_en_i      (dummy_instr_en),      // UNUSED  (output từ cs_register)
    .dummy_instr_mask_i    (dummy_instr_mask),    // UNUSED  (output từ cs_register)
    .dummy_instr_seed_en_i (dummy_instr_seed_en), // UNUSED  (output từ cs_register)
    .dummy_instr_seed_i    (dummy_instr_seed),    // UNUSED  (output từ cs_register)

    .icache_enable_i       (icache_enable),       // NOT CONNECTED  (output từ cs_register)
    .icache_inval_i        (icache_inval),        // CONNECTED ID
    .icache_ecc_error_o    (icache_ecc_error),    // CONNECTED (điều kiện cho alert_minor_o)

    // branch targets
    .branch_target_ex_i(branch_target_ex),        // NOT CONNECTED (từ ex_stage)

    // CSRs
    .csr_mepc_i      (csr_mepc),        // NOT CONNECTED (từ cs_register) // exception return address
    .csr_depc_i      (csr_depc),        // NOT CONNECTED (từ cs_register) // debug return address
    .csr_mtvec_i     (csr_mtvec),       // NOT CONNECTED (từ cs_register) // trap-vector base address
    .csr_mtvec_init_o(csr_mtvec_init),  // NOT CONNECTED (từ cs_register)

    // pipeline stalls
    .id_in_ready_i(id_in_ready),    // NOT CONNECTED (output của controller)

    // misc signals
    .pc_mismatch_alert_o(pc_mismatch_alert),    // NOT CONNECTED  (1 trong các điều kiện của alert_major_internal_o)
    .if_busy_o          (if_busy),    // NOT CONNECTED  (1 trong các điều kiện cho core_busy_o)

    // outputs to ID stage
    .instr_valid_id_o        (instr_valid_id),      // CONNECTED ID  // instr in IF-ID is valid
    .instr_new_id_o          (instr_new_id),        // NOT CONNECTED (điều kiện cho đống RVFI) // instr in IF-ID is new
    .instr_rdata_id_o        (instr_rdata_id),      // CONNECTED ID  // instr for ID stage
    .instr_rdata_alu_id_o    (instr_rdata_alu_id),  // CONNECTED ID  // replicated instr for ID stage to reduce fan-out

    .instr_rdata_c_id_o      (instr_rdata_c_id),        // NOT CONNECTED (đi vào input của controller) // compressed instr for ID stage 
    .instr_is_compressed_id_o(instr_is_compressed_id),  // CONNECTED ID  (cần nối vào wb nữa)
    .instr_bp_taken_o        (instr_bp_taken_id),       // NOT CONNECTED (đi vào input của controller)
    .instr_fetch_err_o       (instr_fetch_err),         // CONNECTED ID
    .instr_fetch_err_plus2_o (instr_fetch_err_plus2),   // NOT CONNECTED (đi vào input của controller)
    .illegal_c_insn_id_o     (illegal_c_insn_id),       // CONNECTED ID
    
    .dummy_instr_id_o        (dummy_instr_id),          //UNUSED
    .pc_if_o                 (pc_if),                   // NOT CONNECTED (đi vào input cs_register)
    .pc_id_o                 (pc_id),                   // CONNECTED ID  (đi vào input cs_register)
    .pmp_err_if_i            (pmp_req_err[PMP_I]),      // NOT CONNECTED (output của ibex_pmp)
    .pmp_err_if_plus2_i      (pmp_req_err[PMP_I2]),     // NOT CONNECTED (output của ibex_pmp)
  );

  // Core is waiting for the ISide when ID/EX stage is ready for a new instruction but none are
  // available
  assign perf_iside_wait = id_in_ready & ~instr_valid_id;

  // Multi-bit fetch enable used when SecureIbex == 1. When SecureIbex == 0 only use the bottom-bit
  // of fetch_enable_i. Ensure the multi-bit encoding has the bottom bit set for on and unset for
  // off so IbexMuBiOn/IbexMuBiOff can be used without needing to know the value of SecureIbex.

  // `ASSERT_INIT(IbexMuBiSecureOnBottomBitSet,    IbexMuBiOn[0] == 1'b1)
  // `ASSERT_INIT(IbexMuBiSecureOffBottomBitClear, IbexMuBiOff[0] == 1'b0)

  // fetch_enable_i can be used to stop the core fetching new instructions
    // For non secure Ibex only the bottom bit of fetch enable is considered
    logic unused_fetch_enable;
    assign unused_fetch_enable = ^fetch_enable_i[$bits(ibex_mubi_t)-1:1];

    assign instr_req_gated = instr_req_int & fetch_enable_i[0];
    assign instr_exec      = fetch_enable_i[0];


  //////////////////////
  //     ID Stage     //
  //////////////////////

  ID_top #(
    .RV32E          (RV32E),
    .RV32M          (RV32M),
    .RV32B          (RV32B),
    .BranchTargetALU(BranchTargetALU),
    .DataIndTiming  (DataIndTiming),
    .WritebackStage (WritebackStage),
    .BranchPredictor(BranchPredictor),
    .MemECC         (MemECC)
  ) id_stage_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // Interface to IF stage
    .instr_valid_i          (instr_valid_id),           // CONNECTED (output từ IF stage)
    .instr_fetch_err_i      (instr_fetch_err),          // CONNECTED (output từ IF stage)
    .instr_rdata_i          (instr_rdata_id),           // CONNECTED (output từ IF stage)   // from IF-ID pipeline registers
    .instr_rdata_alu_i      (instr_rdata_alu_id),       // CONNECTED (output từ IF stage)   // from IF-ID pipeline registers
    .instr_is_compressed_i  (instr_is_compressed_id),   // CONNECTED (output từ IF stage)
    .illegal_c_insn_i       (illegal_c_insn_id),        // CONNECTED (output từ IF stage)
    .pc_id_i                (pc_id),                    // CONNECTED (output từ IF stage)

    // Branch
    .instr_first_cycle_i     (),      // From FSM   // NOT DONE input logic
    .branch_taken_i          (),      // From FSM   // NOT DONE input logic

    // LSU  Interface
    .lsu_req_EX           (lsu_req),  // to load store unit
    .lsu_we_EX            (lsu_we),  // to load store unit
    .lsu_type_EX          (lsu_type),  // to load store unit
    .lsu_sign_ext_EX      (lsu_sign_ext),  // to load store unit
    .lsu_wdata_EX         (lsu_wdata),  // to load store unit

    // MUL, DIV Interface
    .mult_en_EX            (mult_en_ex),    // CONNECTED (tới input ex_stage)
    .div_en_EX             (div_en_ex),     // CONNECTED (tới input ex_stage)
    .mult_sel_EX           (mult_sel_ex),   // CONNECTED (tới input ex_stage)
    .div_sel_EX            (div_sel_ex),    // CONNECTED (tới input ex_stage)
    .multdiv_operator_EX   (multdiv_operator_ex),     // CONNECTED (tới input ex_stage)
    .multdiv_signed_mode_EX(multdiv_signed_mode_ex),  // CONNECTED (tới input ex_stage)

    // CSR
    .csr_access_EX(csr_access),   // CONNECTED (tới input ex_stage)
    .csr_op_EX(csr_op),           // CONNECTED (tới input ex_stage)
    .csr_op_en_EX(csr_op_en),     // CONNECTED (tới input ex_stage)

    // REG_FILE
    // read
    .rf_raddr_a_o      (rf_raddr_a),    // DONE (nối tới REGISTER FILE FPGA)
    .rf_rdata_a_i      (rf_rdata_a),    // DONE (nối tới REGISTER FILE FPGA)
    .rf_raddr_b_o      (rf_raddr_b),    // DONE (nối tới REGISTER FILE FPGA)
    .rf_rdata_b_i      (rf_rdata_b),    // DONE (nối tới REGISTER FILE FPGA)
    .rf_ren_a_o        (rf_ren_a),      // DONE (nối tới REGISTER FILE FPGA)
    .rf_ren_b_o        (rf_ren_b),      // DONE (nối tới REGISTER FILE FPGA)

    .rf_rdata_a_EX      (rf_rdata_a_ex),       // DONE (nối vào input ex_stage) output logic [31:0] 
    .rf_rdata_b_EX      (rf_rdata_b_ex),       // DONE (nối vào input ex_stage) output logic [31:0] 
    // write
    .rf_wdata_sel_EX    (rf_wdata_sel_ex),   // DONE (nối vào input ex_stage)output ibex_pkg::rf_wd_sel_e
    .rf_we_EX           (rf_we_ex),          // DONE (nối vào input ex_stage)output logic
    .rf_waddr_EX        (rf_waddr_ex),       // DONE (nối vào input ex_stage) output logic [4:0]

    // IMM
    .imm_a_mux_sel_EX   (imm_a_mux_sel_ex),   // DONE (nối vào input ex_stage)
    .imm_b_mux_sel_EX   (imm_a_mux_sel_ex),   // DONE (nối vào input ex_stage)

    .instr_EX               (instr_ex),                 // DONE output [31:0]
    .instr_rs1_EX           (instr_rs1_ex),             // DONE output [4:0]
    .instr_rs2_EX           (instr_rs2_ex),             // DONE output [4:0]
    .instr_rs3_EX           (instr_rs3_ex),             // DONE output [4:0]
    .instr_rd_EX            (instr_rd_ex),              // DONE output [4:0]
    .pc_EX                  (pc_ex),                    // DONE output [31:0]
    .instr_is_compressed_EX (instr_is_compressed_ex),   // DONE output logic
      
    .imm_i_type_EX          (imm_i_type_ex),   // DONE (nối vào input ex) output [31:0]
    .imm_b_type_EX          (imm_b_type_ex),   // DONE (nối vào input ex) output [31:0]
    .imm_s_type_EX          (imm_s_type_ex),   // DONE (nối vào input ex) output [31:0]
    .imm_j_type_EX          (imm_j_type_ex),   // DONE (nối vào input ex) output [31:0]
    .imm_u_type_EX          (imm_u_type_ex),   // DONE (nối vào input ex) output [31:0]
    .zimm_rs1_type_EX       (zimm_rs1_type_ex),   // DONE (nối vào input ex) output [31:0]
    
    // BTALU
    .bt_a_mux_sel_EX        (bt_a_mux_sel_EX),   // DONE (nối vào input ex_stage) output op_a_sel_e
    .bt_b_mux_sel_EX        (bt_b_mux_sel_EX),   // DONE (nối vào input ex_stage) output imm_b_sel_e
      
    // ALU
    .alu_operator_EX      (alu_operator_ex),     // NOT DONE output   alu_op_e
    .alu_op_a_mux_sel_EX  (alu_op_a_mux_sel_ex),     // DONE  output  op_a_sel_e
    .alu_op_b_mux_sel_EX  (alu_op_a_mux_sel_ex),     // DONE output  op_b_sel_e
    
    // CONTROLLER INTERFACE
    .illegal_insn_o   (illegal_insn_id),    // DONE (unused) output logic
    .ebrk_insn_o      (ebrk_insn),          // NOT DONE (nối vào controller) output logic
    .mret_insn_o      (mret_insn),          // NOT DONE (nối vào controller) output logic
                                              
    .dret_insn_o      (dret_insn),          // NOT DONE (nối vào controller) output logic
    .ecall_insn_o     (ecall_insn),         // NOT DONE (nối vào controller) output logic
    .wfi_insn_o       (wfi_insn),           // NOT DONE (nối vào controller) output logic
    .jump_set_o       (),           // NOT DONE output logic
    .icache_inval_o   (icache_inval)        // DONE (nối input của if_stage )
  );

  // for RVFI only
  assign unused_illegal_insn_id = illegal_insn_id;

  ///////////////////
  //    EX Stage   //
  ///////////////////

  

  EX_top ex_stage_i (
    .clk_i(clk_i),
    .rst_ni(rst_ni),

    // CSR RDATA
    .csr_rdata_i        (csr_rdata),  // NOT DONE (output từ cs_register)

    // LSU inputs
    .lsu_addr_incr_req_i  (lsu_addr_incr_req),  // NOT DONE (output từ load store unit)
    .lsu_addr_last_i      (lsu_addr_last),      // NOT DONE (output từ load store unit)

    // ID/EX PIPELINE INPUT
    // MUL, DIV INTERFACE
    .mult_en_EX             (mult_en_ex),    // CONNECTED (từ output của id_stage)
    .div_en_EX              (div_en_ex),     // CONNECTED (từ output của id_stage)
    .mult_sel_EX            (mult_sel_ex),   // CONNECTED (từ output của id_stage)
    .div_sel_EX             (div_sel_ex),    // CONNECTED (từ output của id_stage)
    .multdiv_operator_EX    (multdiv_operator_ex),    // CONNECTED (từ output của id_stage)
    .multdiv_signed_mode_EX (multdiv_signed_mode_ex), // CONNECTED (từ output của id_stage)

    .multdiv_ready_id_i   (),   // NOT DONE ( từ FSM )
    .data_ind_timing_i    (),   // NOT DONE ( từ FSM )

    // CSR
    .csr_access_EX(csr_access),  // CONNECTED (từ output của id_stage)
    .csr_op_EX(csr_op),          // CONNECTED (từ output của id_stage)
    .csr_op_en_EX(csr_op_en),    // CONNECTED (từ output của id_stage)

    .rf_rdata_a_EX    (rf_rdata_a_ex),  // DONE (nối từ output id_stage)
    .rf_rdata_b_EX    (rf_rdata_b_ex),  // DONE (nối từ output id_stage)

    // WRITE
    .rf_wdata_sel_EX  (rf_wdata_sel_ex),  // CONNECTED (từ output của id_stage)
    .rf_we_EX         (rf_we_ex),                // CONNECTED (từ output của id_stage)
    .rf_waddr_EX      (rf_waddr_ex),          // CONNECTED (từ output của id_stage)

    // IMM
    .imm_a_mux_sel_EX (imm_a_mux_sel_ex),   // DONE (từ output của id_stage)
    .imm_b_mux_sel_EX (imm_a_mux_sel_ex),  // DONE (từ output của id_stage)

    .instr_EX       (instr_ex),                         // DONE (từ output của id_stage)
    .instr_rs1_EX   (instr_rs1_ex),                     // DONE (từ output của id_stage)
    .instr_rs2_EX   (instr_rs2_ex),                     // DONE (từ output của id_stage)
    .instr_rs3_EX   (instr_rs3_ex),                     // DONE (từ output của id_stage)
    .instr_rd_EX    (instr_rd_ex),                      // DONE (từ output của id_stage)
    .pc_EX          (pc_ex),                            // DONE (từ output của id_stage)
    .instr_is_compressed_EX (instr_is_compressed_ex),   // DONE (từ output của id_stage)

    .imm_i_type_EX    (imm_i_type_ex),      // DONE (từ output của id_stage)
    .imm_b_type_EX    (imm_b_type_ex),      // DONE (từ output của id_stage)
    .imm_s_type_EX    (imm_s_type_ex),      // DONE (từ output của id_stage)
    .imm_j_type_EX    (imm_j_type_ex),      // DONE (từ output của id_stage)
    .imm_u_type_EX    (imm_u_type_ex),      // DONE (từ output của id_stage)
    .zimm_rs1_type_EX (zimm_rs1_type_ex),   // DONE (từ output của id_stage)

    // BTALU
    .bt_a_mux_sel_EX(bt_a_mux_sel_EX),      // DONE (từ output id_stage)
    .bt_b_mux_sel_EX(bt_b_mux_sel_EX),      // DONE (từ output id_stage)

    // ALU
    .alu_operator_EX(alu_operator_ex),
    .alu_op_a_mux_sel_EX(),
    .alu_op_b_mux_sel_EX(),
    .alu_instr_first_cycle_i(),

    // intermediate val reg
    .imd_val_we_o(),    // NOT DONE ()
    .imd_val_d_o(),     // NOT DONE ()
    .imd_val_q_i(),     // NOT DONE ()

    // Outputs
    .alu_adder_result_ex_o(alu_adder_result_ex),
    .branch_target_o(),
    .branch_decision_o(),

    .ex_valid_o(),

    .rf_waddr_EX_o(),
    .rf_wdata_EX_o(rf_wdata_ex),
    .rf_we_EX_o()

  );

  /////////////////////
  // Load/store unit //
  /////////////////////
  assign data_req_o   = data_req_out & ~pmp_req_err[PMP_D];
  assign lsu_resp_err = lsu_load_err | lsu_store_err;

  LSU_top lsu_block_i #(
    .DataWidth      (DataWidth),
    .MemECC         (MemECC),
  )(
    .clk_i(clk_i),
    .rst_ni(rst_ni),

    //data interface
    .data_req_i(data_req_o),
    .data_gnt_i(data_gnt_i),
    .data_rvalid_i(data_rvalid_i),
    .data_bus_err_i(data_err_i),
    .data_pmp_err_i(pmp_req_err[PMP_D]),

    .data_addr_o(data_addr_o),
    .data_wdata_o(data_wdata_o),
    .data_rdata_i(data_rdata_i),
    .data_we_o(data_we_o),
    .data_be_o(data_be_o),

    // signal to/from ID stage
    .lsu_we_i(lsu_we), //From ID
    .lsu_type_i(lsu_type), //from ID
    .lsu_wdata_i(lsu_wdata), //from FW data
    .lsu_sign_ext_i(lsu_sign_ext), //from ID

    .lsu_rdata_o(rf_wdata_lsu), //to WB
    .lsu_rdata_valid_o(lsu_rdata_valid), //to WB
    .lsu_req_i(lsu_req), //from id
    .lsu_req_done_i(lsu_req_done), //to FSM

    .adder_result_ex_i(alu_adder_result_ex), //from EX

    .addr_incr_req_o(lsu_addr_incr_req), //to EX
    .addr_last_o(lsu_addr_last), //to EX

    .lsu_resp_valid_o(lsu_resp_valid), //to FSM

    //exception signals
    .load_err_o(lsu_load_err),
    .load_resp_intg_err_o(lsu_load_resp_intg_err),
    .store_err_o(lsu_store_err),
    .store_resp_intg_err_o(lsu_store_resp_intg_err),

    .busy_o(lsu_busy),

    .perf_load_o(perf_load),
    .perf_store_o(perf_store)
  )


  WB_top wb_stage_i(
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .rf_waddr_EX    (rf_waddr_ex),    // CONNECTED (từ output của ex_stage)
    .rf_wdata_EX    (rf_wdata_ex),    // CONNECTED (từ output của ex_stage)
    .rf_we_EX       (rf_we_ex),       // CONNECTED (từ output của ex_stage)

    .rf_wdata_lsu_i (rf_wdata_lsu),   // CONNECTED (từ output của load store unit)
    .rf_we_lsu_i    (rf_we_lsu),      // CONNECTED (từ output của load store unit)
    
    .rf_wdata_WB_o  (rf_wdata_wb),    // CONNECTED (tới input của regfile)
    .rf_we_WB_o     (rf_we_wb),       // CONNECTED (tới input của regfile)
    .rf_waddr_WB_o  (rf_waddr_wb)    // CONNECTED (tới input của regfile)
  );

    // For non-secure configurations trust the bus protocol is being followed and we'll only ever
    // see a response if we have an outstanding request.
    assign lsu_load_err  = lsu_load_err_raw;
    assign lsu_store_err = lsu_store_err_raw;
    assign rf_we_lsu     = lsu_rdata_valid;

    // expected_load_resp_id/expected_store_resp_id signals are only used to guard against false
    // responses so they are unused in non-secure configurations
    logic unused_expecting_load_resp_id;
    logic unused_expecting_store_resp_id;

    assign unused_expecting_load_resp_id  = expecting_load_resp_id;
    assign unused_expecting_store_resp_id = expecting_store_resp_id;

  // chuyển rf vào trong regfile
  // assign dummy_instr_id_o = dummy_instr_id; nối tín hiệu mặc định 0
  // assign dummy_instr_wb_o = dummy_instr_wb; nối tín hiệu mặc định 0
  // assign rf_raddr_a_o     = rf_raddr_a;
  // assign rf_waddr_wb_o    = rf_waddr_wb;
  // assign rf_we_wb_o       = rf_we_wb;
  // assign rf_raddr_b_o     = rf_raddr_b;    

    logic unused_rf_ren_a, unused_rf_ren_b;
    logic unused_rf_rd_a_wb_match, unused_rf_rd_b_wb_match;

    assign unused_rf_ren_a         = rf_ren_a;
    assign unused_rf_ren_b         = rf_ren_b;
    assign unused_rf_rd_a_wb_match = rf_rd_a_wb_match;
    assign unused_rf_rd_b_wb_match = rf_rd_b_wb_match;
    assign rf_wdata_wb_ecc       = rf_wdata_wb;
    assign rf_rdata_a              = rf_rdata_a_ecc_i;
    assign rf_rdata_b              = rf_rdata_b_ecc_i;
    assign rf_ecc_err_comb         = 1'b0;

  ///////////////////////
  // Crash dump output //
  ///////////////////////

  logic [31:0] crash_dump_mtval;
  assign crash_dump_o.current_pc     = pc_id;
  assign crash_dump_o.next_pc        = pc_if;
  assign crash_dump_o.last_data_addr = lsu_addr_last;
  assign crash_dump_o.exception_pc   = csr_mepc;
  assign crash_dump_o.exception_addr = crash_dump_mtval;

  ///////////////////
  // Alert outputs //
  ///////////////////

  // Minor alert - core is in a recoverable state
  assign alert_minor_o = icache_ecc_error;

  // Major internal alert - core is unrecoverable
  assign alert_major_internal_o = rf_ecc_err_comb | pc_mismatch_alert | csr_shadow_err;
  // Major bus alert
  assign alert_major_bus_o = lsu_load_resp_intg_err | lsu_store_resp_intg_err | instr_intg_err;

`ifdef INC_ASSERT
  // Signals used for assertions only
  logic outstanding_load_resp;
  logic outstanding_store_resp;

  logic outstanding_load_id;
  logic outstanding_store_id;

  assign outstanding_load_id  = id_stage_i.instr_executing & id_stage_i.lsu_req_dec &
                                ~id_stage_i.lsu_we;
  assign outstanding_store_id = id_stage_i.instr_executing & id_stage_i.lsu_req_dec &
                                id_stage_i.lsu_we;

  //if (WritebackStage) begin : gen_wb_stage
    // When the writeback stage is present a load/store could be in ID or WB. A Load/store in ID can
    // see a response before it moves to WB when it is unaligned otherwise we should only see
    // a response when load/store is in WB.
    assign outstanding_load_resp  = outstanding_load_wb |
      (outstanding_load_id  & load_store_unit_i.split_misaligned_access);

    assign outstanding_store_resp = outstanding_store_wb |
      (outstanding_store_id & load_store_unit_i.split_misaligned_access);

    // When writing back the result of a load, the load must have made it to writeback
    `ASSERT(NoMemRFWriteWithoutPendingLoad, rf_we_lsu |-> outstanding_load_wb, clk_i, !rst_ni)
  // end else begin : gen_no_wb_stage
  //   // Without writeback stage only look into whether load or store is in ID to determine if
  //   // a response is expected.
  //   assign outstanding_load_resp  = outstanding_load_id;
  //   assign outstanding_store_resp = outstanding_store_id;

  //   `ASSERT(NoMemRFWriteWithoutPendingLoad, rf_we_lsu |-> outstanding_load_id, clk_i, !rst_ni)
  // end

  `ASSERT(NoMemResponseWithoutPendingAccess,
    data_rvalid_i |-> outstanding_load_resp | outstanding_store_resp, clk_i, !rst_ni)


  // Keep track of the PC last seen in the ID stage when fetch is disabled
  logic [31:0]   pc_at_fetch_disable;
  ibex_mubi_t    last_fetch_enable;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pc_at_fetch_disable <= '0;
      last_fetch_enable   <= '0;
    end else begin
      last_fetch_enable <= fetch_enable_i;

      if ((fetch_enable_i != IbexMuBiOn) && (last_fetch_enable == IbexMuBiOn)) begin
        pc_at_fetch_disable <= pc_id;
      end
    end
  end

  // When fetch is disabled no instructions should be executed. Once fetch is disabled either the
  // ID/EX stage is not valid or the PC of the ID/EX stage must remain as it was at disable. The
  // ID/EX valid should not ressert once it has been cleared.
  `ASSERT(NoExecWhenFetchEnableNotOn, fetch_enable_i != IbexMuBiOn |=>
    (~instr_valid_id || (pc_id == pc_at_fetch_disable)) && ~$rose(instr_valid_id))

  `endif


  ///////////////////
  // Alert outputs //
  ///////////////////

  // Minor alert - core is in a recoverable state
  assign alert_minor_o = icache_ecc_error;

    // Major internal alert - core is unrecoverable
  assign alert_major_internal_o = rf_ecc_err_comb | pc_mismatch_alert | csr_shadow_err;
  // Major bus alert
  assign alert_major_bus_o = lsu_load_resp_intg_err | lsu_store_resp_intg_err | instr_intg_err;

  ////////////////////////
  // RF (Register File) //
  ////////////////////////
  ibex_register_file_fpga #(
    .RV32E          (RV32E),
    .DataWidth      (DataWidth),
    .DummyInstructions(0),
    .WrenCheck      (0),
    .RdataMuxCheck  (0),
    .WordZeroVal    ('0),
  ) rf_i (
    .clk_i(clk_i),
    .rst_ni(rst_ni),

    .raddr_a_i(rf_raddr_a),   // DONE (nối với id_stage)
    .rdata_a_o(rf_rdata_a),   // DONE (nối với id_stage)
    .ren_a_i(rf_ren_a),       // DONE (nối với id_stage)

    .raddr_b_i(rf_raddr_b),   // DONE (nối với id_stage)
    .rdata_b_o(rf_rdata_b),   // DONE (nối với id_stage)
    .ren_b_i(rf_ren_b),       // DONE (nối với id_stage)

    .waddr_i(rf_waddr_wb),      // DONE (từ output của ex_stage)
    .wdata_i(rf_wdata_wb_ecc),  // DONE (assign từ rf_wdata_wb của output ex_stage)
    .we_i(rf_we_wb),            // DONE (từ output của ex_stage)

    .ecc_err_i(rf_ecc_err_comb)   // DONE ( gán = 0)
  );


  //////////////////////
  //  RVFI Interface  //
  //////////////////////

  // 4 stage pipeline requires 3 set (instr_info -> ex -> wb)
  localparam int RVFI_STAGES = 3;

  logic        rvfi_instr_new_wb;
  logic        rvfi_intr_d;
  logic        rvfi_intr_q;
  logic        rvfi_set_trap_pc_d;
  logic        rvfi_set_trap_pc_q;
  logic [31:0] rvfi_insn_id;
  logic [4:0]  rvfi_rs1_addr_d;
  logic [4:0]  rvfi_rs1_addr_q;
  logic [4:0]  rvfi_rs2_addr_d;
  logic [4:0]  rvfi_rs2_addr_q;
  logic [4:0]  rvfi_rs3_addr_d;
  logic [31:0] rvfi_rs1_data_d;
  logic [31:0] rvfi_rs1_data_q;
  logic [31:0] rvfi_rs2_data_d;
  logic [31:0] rvfi_rs2_data_q;
  logic [31:0] rvfi_rs3_data_d;
  logic [4:0]  rvfi_rd_addr_wb;
  logic [4:0]  rvfi_rd_addr_q;
  logic [4:0]  rvfi_rd_addr_d;
  logic [31:0] rvfi_rd_wdata_wb;
  logic [31:0] rvfi_rd_wdata_d;
  logic [31:0] rvfi_rd_wdata_q;
  logic        rvfi_rd_we_wb;
  logic [3:0]  rvfi_mem_mask_int;
  logic [31:0] rvfi_mem_rdata_d;
  logic [31:0] rvfi_mem_rdata_q;
  logic [31:0] rvfi_mem_wdata_d;
  logic [31:0] rvfi_mem_wdata_q;
  logic [31:0] rvfi_mem_addr_d;
  logic [31:0] rvfi_mem_addr_q;
  logic        rvfi_trap_id;
  logic        rvfi_trap_wb;
  logic        rvfi_irq_valid;
  logic [63:0] rvfi_stage_order_d;
  logic        rvfi_id_done;
  logic        rvfi_wb_done;

  logic            new_debug_req;
  logic            new_nmi;
  logic            new_nmi_int;
  logic            new_irq;
  ibex_pkg::irqs_t captured_mip;
  logic            captured_nmi;
  logic            captured_nmi_int;
  logic            captured_debug_req;
  logic            captured_valid;

  // RVFI extension for co-simulation support
  // debug_req and MIP captured at IF -> ID transition so one extra stage
  ibex_pkg::irqs_t rvfi_ext_stage_pre_mip          [RVFI_STAGES+1];
  ibex_pkg::irqs_t rvfi_ext_stage_post_mip         [RVFI_STAGES];
  logic            rvfi_ext_stage_nmi              [RVFI_STAGES+1];
  logic            rvfi_ext_stage_nmi_int          [RVFI_STAGES+1];
  logic            rvfi_ext_stage_debug_req        [RVFI_STAGES+1];
  logic            rvfi_ext_stage_debug_mode       [RVFI_STAGES];
  logic [63:0]     rvfi_ext_stage_mcycle           [RVFI_STAGES];
  logic [31:0]     rvfi_ext_stage_mhpmcounters     [RVFI_STAGES][10];
  logic [31:0]     rvfi_ext_stage_mhpmcountersh    [RVFI_STAGES][10];
  logic            rvfi_ext_stage_ic_scr_key_valid [RVFI_STAGES];
  logic            rvfi_ext_stage_irq_valid        [RVFI_STAGES+1];


  logic        rvfi_stage_valid_d   [RVFI_STAGES];

  logic        rvfi_stage_valid     [RVFI_STAGES];
  logic [63:0] rvfi_stage_order     [RVFI_STAGES];
  logic [31:0] rvfi_stage_insn      [RVFI_STAGES];
  logic        rvfi_stage_trap      [RVFI_STAGES];
  logic        rvfi_stage_halt      [RVFI_STAGES];
  logic        rvfi_stage_intr      [RVFI_STAGES];
  logic [ 1:0] rvfi_stage_mode      [RVFI_STAGES];
  logic [ 1:0] rvfi_stage_ixl       [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rs1_addr  [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rs2_addr  [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rs3_addr  [RVFI_STAGES];
  logic [31:0] rvfi_stage_rs1_rdata [RVFI_STAGES];
  logic [31:0] rvfi_stage_rs2_rdata [RVFI_STAGES];
  logic [31:0] rvfi_stage_rs3_rdata [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rd_addr   [RVFI_STAGES];
  logic [31:0] rvfi_stage_rd_wdata  [RVFI_STAGES];
  logic [31:0] rvfi_stage_pc_rdata  [RVFI_STAGES];
  logic [31:0] rvfi_stage_pc_wdata  [RVFI_STAGES];
  logic [31:0] rvfi_stage_mem_addr  [RVFI_STAGES];
  logic [ 3:0] rvfi_stage_mem_rmask [RVFI_STAGES];
  logic [ 3:0] rvfi_stage_mem_wmask [RVFI_STAGES];
  logic [31:0] rvfi_stage_mem_rdata [RVFI_STAGES];
  logic [31:0] rvfi_stage_mem_wdata [RVFI_STAGES];

  assign rvfi_valid     = rvfi_stage_valid    [RVFI_STAGES-1];
  assign rvfi_order     = rvfi_stage_order    [RVFI_STAGES-1];
  assign rvfi_insn      = rvfi_stage_insn     [RVFI_STAGES-1];
  assign rvfi_trap      = rvfi_stage_trap     [RVFI_STAGES-1];
  assign rvfi_halt      = rvfi_stage_halt     [RVFI_STAGES-1];
  assign rvfi_intr      = rvfi_stage_intr     [RVFI_STAGES-1];
  assign rvfi_mode      = rvfi_stage_mode     [RVFI_STAGES-1];
  assign rvfi_ixl       = rvfi_stage_ixl      [RVFI_STAGES-1];
  assign rvfi_rs1_addr  = rvfi_stage_rs1_addr [RVFI_STAGES-1];
  assign rvfi_rs2_addr  = rvfi_stage_rs2_addr [RVFI_STAGES-1];
  assign rvfi_rs3_addr  = rvfi_stage_rs3_addr [RVFI_STAGES-1];
  assign rvfi_rs1_rdata = rvfi_stage_rs1_rdata[RVFI_STAGES-1];
  assign rvfi_rs2_rdata = rvfi_stage_rs2_rdata[RVFI_STAGES-1];
  assign rvfi_rs3_rdata = rvfi_stage_rs3_rdata[RVFI_STAGES-1];
  assign rvfi_rd_addr   = rvfi_stage_rd_addr  [RVFI_STAGES-1];
  assign rvfi_rd_wdata  = rvfi_stage_rd_wdata [RVFI_STAGES-1];
  assign rvfi_pc_rdata  = rvfi_stage_pc_rdata [RVFI_STAGES-1];
  assign rvfi_pc_wdata  = rvfi_stage_pc_wdata [RVFI_STAGES-1];
  assign rvfi_mem_addr  = rvfi_stage_mem_addr [RVFI_STAGES-1];
  assign rvfi_mem_rmask = rvfi_stage_mem_rmask[RVFI_STAGES-1];
  assign rvfi_mem_wmask = rvfi_stage_mem_wmask[RVFI_STAGES-1];
  assign rvfi_mem_rdata = rvfi_stage_mem_rdata[RVFI_STAGES-1];
  assign rvfi_mem_wdata = rvfi_stage_mem_wdata[RVFI_STAGES-1];

endmodule
