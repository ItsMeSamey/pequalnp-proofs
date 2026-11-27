import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Order.Interval.Finset.Nat

/-! Fixed producer charges for the ordered prefix of the SHA-256 pinned
fresh-mux-170-14.json. Wire 20 is a free raw input. Paid IDs are original
gate wires 64..219, not coordinates of the replacement decoder. -/
namespace Enriched30Retained

abbrev Row := Nat × List Nat

def bank : List Nat :=
  [20,84,89,90,101,103,115,125,130,136,137,145,157,158,163,167,170,178,181,182,189,190,193,199,203,207,208,210,214,219]

def mandatorySlots : Finset Nat := ((Finset.range 30).erase 3).erase 10

def mandatoryWires : Finset Nat :=
  [20,84,89,101,103,115,125,130,136,145,157,158,163,167,170,178,181,182,189,190,193,199,203,207,208,210,214,219].toFinset

theorem slot_image :
    mandatorySlots.image (fun j => bank.getD j 0) = mandatoryWires := by decide +kernel

/- Rows in descending output-wire order. The input list of each row retains
the original pin order, including a single pin for the marker NOT. -/
def prefixRows : List Row := [
  (219, [213, 218]),
  (218, [214, 217]),
  (217, [117, 216]),
  (216, [95, 215]),
  (215, [40, 116]),
  (214, [118, 211]),
  (213, [123, 212]),
  (212, [125, 211]),
  (211, [35, 109]),
  (210, [73, 209]),
  (209, [33, 78]),
  (208, [206, 207]),
  (207, [120, 159]),
  (206, [179, 205]),
  (205, [172, 204]),
  (204, [31, 59]),
  (203, [201, 202]),
  (202, [38, 86]),
  (201, [87, 200]),
  (200, [13, 27]),
  (199, [195, 198]),
  (198, [152, 197]),
  (197, [91, 196]),
  (196, [24, 34]),
  (195, [121, 194]),
  (194, [80, 193]),
  (193, [45, 192]),
  (192, [32, 191]),
  (191, [6, 14]),
  (190, [185, 189]),
  (189, [146, 188]),
  (188, [111, 187]),
  (187, [91, 186]),
  (186, [22, 37]),
  (185, [171, 184]),
  (184, [126, 183]),
  (183, [14, 39]),
  (182, [68, 181]),
  (181, [132, 180]),
  (180, [41, 179]),
  (179, [75, 153]),
  (178, [170, 177]),
  (177, [171, 176]),
  (176, [172, 175]),
  (175, [93, 174]),
  (174, [147, 173]),
  (173, [18, 38]),
  (172, [12, 55]),
  (171, [53, 100]),
  (170, [99, 169]),
  (169, [116, 168]),
  (168, [19, 31]),
  (167, [163, 166]),
  (166, [110, 165]),
  (165, [70, 164]),
  (164, [75, 100]),
  (163, [82, 162]),
  (162, [159, 161]),
  (161, [46, 160]),
  (160, [1, 28]),
  (159, [54, 76]),
  (158, [151, 157]),
  (157, [152, 156]),
  (156, [153, 155]),
  (155, [57, 154]),
  (154, [3, 26]),
  (153, [4, 61]),
  (152, [55, 133]),
  (151, [146, 150]),
  (150, [64, 149]),
  (149, [147, 148]),
  (148, [0, 56]),
  (147, [28, 36]),
  (146, [16, 60]),
  (145, [141, 144]),
  (144, [92, 143]),
  (143, [108, 142]),
  (142, [4, 16]),
  (141, [124, 140]),
  (140, [59, 139]),
  (139, [52, 138]),
  (138, [51, 117]),
  (137, [130, 136]),
  (136, [132, 135]),
  (135, [133, 134]),
  (134, [44, 65]),
  (133, [1, 42]),
  (132, [15, 131]),
  (131, [28, 50]),
  (130, [126, 129]),
  (129, [80, 128]),
  (128, [59, 127]),
  (127, [7, 22]),
  (126, [34, 74]),
  (125, [23, 124]),
  (124, [18, 37]),
  (123, [120, 122]),
  (122, [50, 121]),
  (121, [21, 48]),
  (120, [60, 119]),
  (119, [24, 27]),
  (118, [42, 104]),
  (117, [9, 24]),
  (116, [17, 45]),
  (115, [107, 114]),
  (114, [110, 113]),
  (113, [111, 112]),
  (112, [11, 53]),
  (111, [26, 32]),
  (110, [108, 109]),
  (109, [15, 36]),
  (108, [3, 41]),
  (107, [104, 106]),
  (106, [79, 105]),
  (105, [14, 65]),
  (104, [19, 52]),
  (103, [97, 102]),
  (102, [99, 101]),
  (101, [81, 100]),
  (100, [6, 10]),
  (99, [85, 98]),
  (98, [0, 61]),
  (97, [92, 96]),
  (96, [93, 95]),
  (95, [11, 94]),
  (94, [30, 46]),
  (93, [44, 52]),
  (92, [62, 91]),
  (91, [8, 40]),
  (90, [84, 89]),
  (89, [86, 88]),
  (88, [64, 87]),
  (87, [2, 18]),
  (86, [48, 85]),
  (85, [47, 54]),
  (84, [82, 83]),
  (83, [49, 63]),
  (82, [79, 81]),
  (81, [21, 80]),
  (80, [25, 43]),
  (79, [4, 58]),
  (78, [74, 77]),
  (77, [75, 76]),
  (76, [5, 20]),
  (75, [9, 39]),
  (74, [0, 62]),
  (73, [23, 72]),
  (72, [70, 71]),
  (71, [45, 63]),
  (70, [2, 51]),
  (69, [68]),
  (68, [64, 67]),
  (67, [65, 66]),
  (66, [10, 57]),
  (65, [13, 33]),
  (64, [29, 35])]

def ProducerClosed (rows : List Row) (paid : Finset Nat) : Prop :=
  ∀ r ∈ rows, r.1 ∈ paid → ∀ w ∈ r.2, 64 ≤ w → w ∈ paid

def addPins (r : Row) (s : Finset Nat) : Finset Nat :=
  if r.1 ∈ s then (r.2.toFinset.filter (fun w => 64 ≤ w)) ∪ s else s

def scan : List Row → Finset Nat → Finset Nat
  | [], s => s
  | r :: rs, s => scan rs (addPins r s)

theorem scan_subset {rows : List Row} {paid s : Finset Nat}
    (closed : ProducerClosed rows paid) (base : s ⊆ paid) : scan rows s ⊆ paid := by
  induction rows generalizing s with
  | nil => exact base
  | cons r rs ih =>
    apply ih
    · intro a ha
      exact closed a (List.mem_cons_of_mem r ha)
    · unfold addPins
      split
      next hr =>
        apply Finset.union_subset
        · intro w hw
          obtain ⟨hp, hi⟩ := Finset.mem_filter.mp hw
          exact closed r (by simp) (base hr) w (List.mem_toFinset.mp hp) hi
        · exact base
      next => exact base

def requiredRoots : Finset Nat := mandatoryWires.filter (fun w => 64 ≤ w)
def requiredOnly : Finset Nat := scan prefixRows requiredRoots
def requiredWithAnchor : Finset Nat := scan prefixRows (insert 69 requiredRoots)
def allPrefix : Finset Nat := Finset.Ico 64 220

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem requiredOnly_eq :
    requiredOnly = ((allPrefix.erase 69).erase 90).erase 137 := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem requiredWithAnchor_eq :
    requiredWithAnchor = (allPrefix.erase 90).erase 137 := by decide +kernel

theorem requiredOnly_card : requiredOnly.card = 153 := by
  rw [requiredOnly_eq]
  decide +kernel

theorem requiredWithAnchor_card : requiredWithAnchor.card = 154 := by
  rw [requiredWithAnchor_eq]
  decide +kernel

theorem requiredRoots_subset (paid : Finset Nat)
    (hm : ∀ w ∈ mandatoryWires, 64 ≤ w → w ∈ paid) : requiredRoots ⊆ paid := by
  intro w hw
  obtain ⟨h, hi⟩ := Finset.mem_filter.mp hw
  exact hm w h hi

theorem retained_unanchored_card_le (paid : Finset Nat)
    (hm : ∀ w ∈ mandatoryWires, 64 ≤ w → w ∈ paid)
    (closed : ProducerClosed prefixRows paid) : 153 ≤ paid.card := by
  rw [← requiredOnly_card]
  exact Finset.card_le_card (scan_subset closed (requiredRoots_subset paid hm))

theorem retained_card_le (paid : Finset Nat)
    (hm : ∀ w ∈ mandatoryWires, 64 ≤ w → w ∈ paid) (anchor : 69 ∈ paid)
    (closed : ProducerClosed prefixRows paid) : 154 ≤ paid.card := by
  rw [← requiredWithAnchor_card]
  apply Finset.card_le_card
  apply scan_subset closed
  exact Finset.insert_subset anchor (requiredRoots_subset paid hm)

/-- A replacement suffix has its own local input coordinates. Faithful physical
attachment sends each live paid donor coordinate to the corresponding prefix wire.
Raw input 20 is attached without adding it to the paid gate set. -/
theorem retained_of_attached_slots (paid liveSlots : Finset Nat)
    (pivotal : mandatorySlots ⊆ liveSlots)
    (attach : ∀ j ∈ liveSlots, 64 ≤ bank.getD j 0 → bank.getD j 0 ∈ paid)
    (anchor : 69 ∈ paid) (closed : ProducerClosed prefixRows paid) :
    154 ≤ paid.card := by
  apply retained_card_le paid _ anchor closed
  intro w hw hgate
  rw [← slot_image] at hw
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
  exact attach j (pivotal hj) hgate

end Enriched30Retained
