### JG and initial blocks
JasperGold ignores inital statements when executing, was an issue when trying to test the verilog.

### Implicit Assumptions

```verilog
assume_no_full_write: assume property (@(posedge clk) disable iff (rst)
                                        // Not the best way to assume, not incorrect though
                                        !(in_write_ctrl && out_is_full));

                                        // Now we're cookin', overlapping implication better for assumptions.
                                        out_is_full |-> !in_write_ctrl
```