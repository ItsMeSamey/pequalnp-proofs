import Std

namespace ThresholdStarWindow

set_option maxRecDepth 64000
set_option maxHeartbeats 0

/-- Rotation of a point or tag seed in its 13-bit lane for the indexed signed sample. -/
def nativePart (seed offset count row : Nat) : Nat :=
  (List.range count).foldl (fun m j =>
    if seed.testBit (row - row%13 + (row+26-j-offset)%13) then m ||| 2^j else m) 0

def nativeMask (r : Nat) : Nat :=
  nativePart 98208053665763697915243686326406377207215194159933986590250855894748600762494670591627578999818636021819886278138988895864059712492579563743896212826002452669388629497739076806458944222402781631192498177 0 13 r |||
    (nativePart 12314279822864772337669408815584145526389919134096398324549342768683350925941497934626908269085097565564298821842084768953647673353807136187280627266975967593137240168264162503943589536258748122593763329 6 7 r <<< 13)

def positiveRow (r : Nat) : Bool :=
  decide (r < 676) && (4503599627370495 : Nat).testBit r && !((34638844649535 : Nat).testBit r)
def negativeRow (r : Nat) : Bool :=
  decide (r < 676) && !((4503599627370495 : Nat).testBit r)

def goodRows : List (Nat × Nat) := [
  (6,8256), (7,16512), (8,33024), (9,66048), (10,132096),
  (11,264192), (12,528384), (19,8320), (20,16640), (21,33280),
  (22,66560), (23,133120), (24,266240), (25,524289), (32,8704),
  (33,17408), (34,34816), (35,69632), (36,131073), (37,262146),
  (38,524292), (45,8196), (46,16392), (47,32784), (48,65568),
  (49,131136), (50,262272), (51,524544)]
def badRows : Array (Nat × Nat) := #[
  (52,114695), (53,229390), (54,458780), (55,925752), (56,802928),
  (57,557280), (58,65984), (59,131968), (60,263936), (61,527872),
  (62,15360), (63,30721), (64,61443), (65,787568), (67,4544),
  (77,918072), (78,279073), (81,143624), (83,566306), (84,84036),
  (85,168072), (86,336145), (87,672290), (88,296004), (89,592008),
  (91,37956), (102,271633), (103,543266), (104,360521), (105,721042),
  (106,393508), (110,21056), (112,76034), (113,152068), (114,304137),
  (115,616466), (116,184356), (129,600090), (131,729114), (132,409652),
  (133,819304), (140,46081), (141,92163), (159,467224), (160,934448),
  (177,49191), (178,98382), (179,196764), (180,401720), (187,550946),
  (190,205074), (207,535586), (286,344085), (287,696362), (289,688296),
  (290,328016), (291,656032), (298,176138), (313,608322), (342,795672),
  (365,679986), (366,311396), (367,622792), (387,159794), (494,376901),
  (495,753802), (506,192546), (519,663610), (601,828456)]
def bad (j : Fin 69) : Nat × Nat := badRows[j.val]!


def rowCheck (j : Nat) : Bool :=
  (List.range 69).all fun k => (j == k) || goodRows.any fun r =>
    (r.2 &&& (badRows[j]!.2 ||| badRows[k]!.2)) == r.2

def goodCheck (r : Nat × Nat) := positiveRow r.1 && (nativeMask r.1 == r.2)
def badCheck (j : Nat) := negativeRow badRows[j]!.1 && (nativeMask badRows[j]!.1 == badRows[j]!.2)
private theorem rowCheck_0 : (List.range' 0 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_2 : (List.range' 2 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_4 : (List.range' 4 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_6 : (List.range' 6 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_8 : (List.range' 8 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_10 : (List.range' 10 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_12 : (List.range' 12 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_14 : (List.range' 14 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_16 : (List.range' 16 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_18 : (List.range' 18 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_20 : (List.range' 20 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_22 : (List.range' 22 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_24 : (List.range' 24 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_26 : (List.range' 26 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_28 : (List.range' 28 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_30 : (List.range' 30 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_32 : (List.range' 32 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_34 : (List.range' 34 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_36 : (List.range' 36 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_38 : (List.range' 38 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_40 : (List.range' 40 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_42 : (List.range' 42 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_44 : (List.range' 44 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_46 : (List.range' 46 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_48 : (List.range' 48 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_50 : (List.range' 50 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_52 : (List.range' 52 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_54 : (List.range' 54 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_56 : (List.range' 56 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_58 : (List.range' 58 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_60 : (List.range' 60 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_62 : (List.range' 62 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_64 : (List.range' 64 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_66 : (List.range' 66 2).all rowCheck = true := by decide +kernel
private theorem rowCheck_68 : (List.range' 68 1).all rowCheck = true := by decide +kernel

theorem rowCheck_ok (j : Nat) (hj : j < 69) : rowCheck j = true := by
  by_cases h0 : j < 2
  · exact List.all_eq_true.mp rowCheck_0 j (by simp only [List.mem_range'_1]; omega)
  by_cases h2 : j < 4
  · exact List.all_eq_true.mp rowCheck_2 j (by simp only [List.mem_range'_1]; omega)
  by_cases h4 : j < 6
  · exact List.all_eq_true.mp rowCheck_4 j (by simp only [List.mem_range'_1]; omega)
  by_cases h6 : j < 8
  · exact List.all_eq_true.mp rowCheck_6 j (by simp only [List.mem_range'_1]; omega)
  by_cases h8 : j < 10
  · exact List.all_eq_true.mp rowCheck_8 j (by simp only [List.mem_range'_1]; omega)
  by_cases h10 : j < 12
  · exact List.all_eq_true.mp rowCheck_10 j (by simp only [List.mem_range'_1]; omega)
  by_cases h12 : j < 14
  · exact List.all_eq_true.mp rowCheck_12 j (by simp only [List.mem_range'_1]; omega)
  by_cases h14 : j < 16
  · exact List.all_eq_true.mp rowCheck_14 j (by simp only [List.mem_range'_1]; omega)
  by_cases h16 : j < 18
  · exact List.all_eq_true.mp rowCheck_16 j (by simp only [List.mem_range'_1]; omega)
  by_cases h18 : j < 20
  · exact List.all_eq_true.mp rowCheck_18 j (by simp only [List.mem_range'_1]; omega)
  by_cases h20 : j < 22
  · exact List.all_eq_true.mp rowCheck_20 j (by simp only [List.mem_range'_1]; omega)
  by_cases h22 : j < 24
  · exact List.all_eq_true.mp rowCheck_22 j (by simp only [List.mem_range'_1]; omega)
  by_cases h24 : j < 26
  · exact List.all_eq_true.mp rowCheck_24 j (by simp only [List.mem_range'_1]; omega)
  by_cases h26 : j < 28
  · exact List.all_eq_true.mp rowCheck_26 j (by simp only [List.mem_range'_1]; omega)
  by_cases h28 : j < 30
  · exact List.all_eq_true.mp rowCheck_28 j (by simp only [List.mem_range'_1]; omega)
  by_cases h30 : j < 32
  · exact List.all_eq_true.mp rowCheck_30 j (by simp only [List.mem_range'_1]; omega)
  by_cases h32 : j < 34
  · exact List.all_eq_true.mp rowCheck_32 j (by simp only [List.mem_range'_1]; omega)
  by_cases h34 : j < 36
  · exact List.all_eq_true.mp rowCheck_34 j (by simp only [List.mem_range'_1]; omega)
  by_cases h36 : j < 38
  · exact List.all_eq_true.mp rowCheck_36 j (by simp only [List.mem_range'_1]; omega)
  by_cases h38 : j < 40
  · exact List.all_eq_true.mp rowCheck_38 j (by simp only [List.mem_range'_1]; omega)
  by_cases h40 : j < 42
  · exact List.all_eq_true.mp rowCheck_40 j (by simp only [List.mem_range'_1]; omega)
  by_cases h42 : j < 44
  · exact List.all_eq_true.mp rowCheck_42 j (by simp only [List.mem_range'_1]; omega)
  by_cases h44 : j < 46
  · exact List.all_eq_true.mp rowCheck_44 j (by simp only [List.mem_range'_1]; omega)
  by_cases h46 : j < 48
  · exact List.all_eq_true.mp rowCheck_46 j (by simp only [List.mem_range'_1]; omega)
  by_cases h48 : j < 50
  · exact List.all_eq_true.mp rowCheck_48 j (by simp only [List.mem_range'_1]; omega)
  by_cases h50 : j < 52
  · exact List.all_eq_true.mp rowCheck_50 j (by simp only [List.mem_range'_1]; omega)
  by_cases h52 : j < 54
  · exact List.all_eq_true.mp rowCheck_52 j (by simp only [List.mem_range'_1]; omega)
  by_cases h54 : j < 56
  · exact List.all_eq_true.mp rowCheck_54 j (by simp only [List.mem_range'_1]; omega)
  by_cases h56 : j < 58
  · exact List.all_eq_true.mp rowCheck_56 j (by simp only [List.mem_range'_1]; omega)
  by_cases h58 : j < 60
  · exact List.all_eq_true.mp rowCheck_58 j (by simp only [List.mem_range'_1]; omega)
  by_cases h60 : j < 62
  · exact List.all_eq_true.mp rowCheck_60 j (by simp only [List.mem_range'_1]; omega)
  by_cases h62 : j < 64
  · exact List.all_eq_true.mp rowCheck_62 j (by simp only [List.mem_range'_1]; omega)
  by_cases h64 : j < 66
  · exact List.all_eq_true.mp rowCheck_64 j (by simp only [List.mem_range'_1]; omega)
  by_cases h66 : j < 68
  · exact List.all_eq_true.mp rowCheck_66 j (by simp only [List.mem_range'_1]; omega)
  exact List.all_eq_true.mp rowCheck_68 j (by simp only [List.mem_range'_1]; omega)

private theorem badCheck_0 : (List.range' 0 6).all badCheck = true := by decide +kernel
private theorem badCheck_6 : (List.range' 6 6).all badCheck = true := by decide +kernel
private theorem badCheck_12 : (List.range' 12 6).all badCheck = true := by decide +kernel
private theorem badCheck_18 : (List.range' 18 6).all badCheck = true := by decide +kernel
private theorem badCheck_24 : (List.range' 24 6).all badCheck = true := by decide +kernel
private theorem badCheck_30 : (List.range' 30 6).all badCheck = true := by decide +kernel
private theorem badCheck_36 : (List.range' 36 6).all badCheck = true := by decide +kernel
private theorem badCheck_42 : (List.range' 42 6).all badCheck = true := by decide +kernel
private theorem badCheck_48 : (List.range' 48 6).all badCheck = true := by decide +kernel
private theorem badCheck_54 : (List.range' 54 6).all badCheck = true := by decide +kernel
private theorem badCheck_60 : (List.range' 60 6).all badCheck = true := by decide +kernel
private theorem badCheck_66 : (List.range' 66 3).all badCheck = true := by decide +kernel

theorem badCheck_ok (j : Nat) (hj : j < 69) : badCheck j = true := by
  by_cases h0 : j < 6
  · exact List.all_eq_true.mp badCheck_0 j (by simp only [List.mem_range'_1]; omega)
  by_cases h6 : j < 12
  · exact List.all_eq_true.mp badCheck_6 j (by simp only [List.mem_range'_1]; omega)
  by_cases h12 : j < 18
  · exact List.all_eq_true.mp badCheck_12 j (by simp only [List.mem_range'_1]; omega)
  by_cases h18 : j < 24
  · exact List.all_eq_true.mp badCheck_18 j (by simp only [List.mem_range'_1]; omega)
  by_cases h24 : j < 30
  · exact List.all_eq_true.mp badCheck_24 j (by simp only [List.mem_range'_1]; omega)
  by_cases h30 : j < 36
  · exact List.all_eq_true.mp badCheck_30 j (by simp only [List.mem_range'_1]; omega)
  by_cases h36 : j < 42
  · exact List.all_eq_true.mp badCheck_36 j (by simp only [List.mem_range'_1]; omega)
  by_cases h42 : j < 48
  · exact List.all_eq_true.mp badCheck_42 j (by simp only [List.mem_range'_1]; omega)
  by_cases h48 : j < 54
  · exact List.all_eq_true.mp badCheck_48 j (by simp only [List.mem_range'_1]; omega)
  by_cases h54 : j < 60
  · exact List.all_eq_true.mp badCheck_54 j (by simp only [List.mem_range'_1]; omega)
  by_cases h60 : j < 66
  · exact List.all_eq_true.mp badCheck_60 j (by simp only [List.mem_range'_1]; omega)
  exact List.all_eq_true.mp badCheck_66 j (by simp only [List.mem_range'_1]; omega)


theorem goodRows_native : goodRows.all goodCheck = true := by decide +kernel

theorem badRows_native (j : Fin 69) :
    negativeRow (bad j).1 = true ∧ nativeMask (bad j).1 = (bad j).2 := by
  have h := badCheck_ok j.val j.isLt
  simpa only [badCheck, bad, Bool.and_eq_true, beq_iff_eq] using h

theorem native_clashes (j k : Fin 69) (hj : j ≠ k) :
    goodRows.any (fun r => (r.2 &&& ((bad j).2 ||| (bad k).2)) == r.2) = true := by
  have hv : j.val ≠ k.val := fun h => hj (Fin.ext h)
  have h := List.all_eq_true.mp (rowCheck_ok j.val j.isLt) k.val (List.mem_range.mpr k.isLt)
  simpa [bad, hv] using h

end ThresholdStarWindow
#print axioms ThresholdStarWindow.native_clashes
