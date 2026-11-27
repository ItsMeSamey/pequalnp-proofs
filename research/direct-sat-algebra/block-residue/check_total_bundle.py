import check_collective_bundle_04
import check_biclique_physical_raw
import check_dual_period_raw
import check_total_p4_raw

if __name__ == "__main__":
    check_biclique_physical_raw.main()
    check_dual_period_raw.main()
    check_total_p4_raw.run(0)
    check_total_p4_raw.run(1)
