# ------------------------------------------
# CSEE6863 - Columbia University
# 8 bit RISC Processor Verification Project
# Hardware group 1
# 	- Michael John Flynn: mf3657
# 	- Felipe Andrade: fga2116
# ------------------------------------------

# Analyze design under verifcation files
set ROOT_PATH ../design

analyze -sv \
	${ROOT_PATH}/processor_top.v \
	${ROOT_PATH}/processor_core.v \
	${ROOT_PATH}/instr_and_data_mem.v \
	${ROOT_PATH}/register_file.v

# We will place assertions directly into our .sv
# But if using .sva files use the following
# analyze -sva \
# 	${PROP_PATH}/generic.sva

elaborate -top processor_top

clock clk
reset ~reset

# Get design information to check general complexity
get_design_info

# Prove properties
prove -all
#autoprove -time_limit 1h

# Report proof results
report

