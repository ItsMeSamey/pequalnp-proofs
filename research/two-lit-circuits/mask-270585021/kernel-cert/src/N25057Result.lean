import N25057Part000
import N25057Part001
import N25057Part002
import N25057Part003
import N25057Part004
import N25057Part005
import N25057Part006
import N25057Part007
import N25057Part008
import N25057Part009
import N25057Part010
import N25057Part011
import N25057Part012
import N25057Part013
import N25057Part014
import N25057Part015
import N25057Part016
import N25057Part017
import N25057Part018
import N25057Part019
import N25057Part020
import N25057Part021
import N25057Part022
import N25057Part023
import N25057Part024
import N25057Part025
import N25057Part026
import N25057Part027
import N25057Part028
import N25057Part029
import N25057Part030
import N25057Part031
import N25057Part032
import N25057Part033
import N25057Part034
import N25057Part035
import N25057Part036
import N25057Part037
import N25057Part038
import N25057Part039
import N25057Part040
import N25057Part041
import N25057Part042
import N25057Part043
import N25057Part044
import N25057Part045
import N25057Part046
import N25057Part047
import N25057Part048
import N25057Part049
import N25057Part050
import N25057Part051
import N25057Part052
import N25057Part053
import N25057Part054
import N25057Part055
import N25057Part056
import N25057Part057
import N25057Part058
import N25057Part059
import N25057Part060
import N25057Part061
import N25057Part062
import N25057Part063
import N25057Part064
import N25057Part065
import N25057Part066
import N25057Part067
import N25057Part068
import N25057Part069
import N25057Part070
import N25057Part071
import N25057Part072
import N25057Part073
namespace Numeric25057
set_option maxRecDepth 200000
theorem covered1181 : Covered table 1181 := advance1181 (advance1168 (advance1152 (advance1136 (advance1120 (advance1104 (advance1088 (advance1072 (advance1056 (advance1040 (advance1024 (advance1008 (advance992 (advance976 (advance960 (advance944 (advance928 (advance912 (advance896 (advance880 (advance864 (advance848 (advance832 (advance816 (advance800 (advance784 (advance768 (advance752 (advance736 (advance720 (advance704 (advance688 (advance672 (advance656 (advance640 (advance624 (advance608 (advance592 (advance576 (advance560 (advance544 (advance528 (advance512 (advance496 (advance480 (advance464 (advance448 (advance432 (advance416 (advance400 (advance384 (advance368 (advance352 (advance336 (advance320 (advance304 (advance288 (advance272 (advance256 (advance240 (advance224 (advance208 (advance192 (advance176 (advance160 (advance144 (advance128 (advance112 (advance96 (advance80 (advance64 (advance48 (advance32 (advance16 (covered_zero table))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem table_card : table.size = 1181 := by simp [table]
theorem allRows : Covered table table.size := by rw [table_card]; exact covered1181
theorem root0 : checkChild table (9,0,start) 261 = true := by rw [childWith_eq table_at]; decide +kernel
theorem root1 : checkChild table (8,1,start) 2360 = true := by rw [childWith_eq table_at]; decide +kernel
theorem root2 : checkChild table (7,2,start) 2358 = true := by rw [childWith_eq table_at]; decide +kernel
theorem root3 : checkChild table (6,3,start) 2356 = true := by rw [childWith_eq table_at]; decide +kernel
theorem root4 : checkChild table (5,4,start) 316463 = true := by rw [childWith_eq table_at]; decide +kernel
end Numeric25057
