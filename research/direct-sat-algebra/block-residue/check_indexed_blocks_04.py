"""Original indexed comparison, private-connector, and autarky controls."""
import check_balanced_branch_raw
import check_branch_nand_04
import check_mux_single_block_04
import check_autarky_oracle

if __name__ == "__main__":
    for control in (check_balanced_branch_raw, check_branch_nand_04,
                    check_mux_single_block_04, check_autarky_oracle):
        control.main()
