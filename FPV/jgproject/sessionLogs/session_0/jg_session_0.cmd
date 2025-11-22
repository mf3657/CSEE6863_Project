# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2024.06
# platform  : Linux 4.18.0-553.83.1.el8_10.x86_64
# version   : 2024.06p002 64 bits
# build date: 2024.09.02 16:28:38 UTC
# ----------------------------------------
# started   : 2025-11-22 18:52:44 EST
# hostname  : micro11.(none)
# pid       : 566386
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:35557' '-style' 'windows' '-data' 'AAAAkHicY2RgYLCp////PwMYMD6A0Aw2jAyoAMRnQhUJbEChGRhYYZphSkAaOBh0GdIYChjKgGwZBjeGAIYwhnggv4ghnyEZyCpj0GMoAbJywDoAwvkNpA==' '-proj' '/homes/user/stud/fall24/fga2116/FV/CSEE6863_Project/FPV/jgproject/sessionLogs/session_0' '-init' '-hidden' '/homes/user/stud/fall24/fga2116/FV/CSEE6863_Project/FPV/jgproject/.tmp/.initCmds.tcl' 'FPV_proc_v.tcl'
# ------------------------------------------
# CSEE6863 - Columbia University
# FIFO example FPV introduction
# Hardware group 1
# 	- Michael John Flynn: mf3657
# 	- Felipe Andrade: fga2116
# ------------------------------------------

# Analyze design under verifcation files
set ROOT_PATH ../design

analyze -sv \
	${ROOT_PATH}/proc.v

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

