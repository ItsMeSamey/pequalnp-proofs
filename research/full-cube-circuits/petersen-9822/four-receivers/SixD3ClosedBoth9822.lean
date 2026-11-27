import SixD3Roster9822
import SixD3RootA0139822
import SixD3RootB0139822
import SixD3RootA0179822
import SixD3RootB0179822
import SixD3RootA0189822
import SixD3RootB0189822
import SixD3RootA0199822
import SixD3RootB0199822
import SixD3RootA0239822
import SixD3RootB0239822
import SixD3RootA0269822
import SixD3RootB0269822
import SixD3RootA0289822
import SixD3RootB0289822
import SixD3RootA0299822
import SixD3RootB0299822
import SixD3RootA0369822
import SixD3RootB0369822
import SixD3RootA0379822
import SixD3RootB0379822
import SixD3RootA0399822
import SixD3RootB0399822
import SixD3RootA0679822
import SixD3RootB0679822
import SixD3RootA0789822
import SixD3RootB0789822
import SixD3RootA0899822
import SixD3RootB0899822
import SixD3RootA1359822
import SixD3RootB1359822
import SixD3RootA1379822
import SixD3RootB1379822
import SixD3RootA1399822
import SixD3RootB1399822
import SixD3RootA1459822
import SixD3RootB1459822
import SixD3RootA1479822
import SixD3RootB1479822
import SixD3RootA1489822
import SixD3RootB1489822
import SixD3RootA1599822
import SixD3RootB1599822
import SixD3RootA1789822
import SixD3RootB1789822
import SixD3RootA1899822
import SixD3RootB1899822
import SixD3RootA2359822
import SixD3RootB2359822
import SixD3RootA2369822
import SixD3RootB2369822
import SixD3RootA2399822
import SixD3RootB2399822
import SixD3RootA2459822
import SixD3RootB2459822
import SixD3RootA2469822
import SixD3RootB2469822
import SixD3RootA2489822
import SixD3RootB2489822
import SixD3RootA2569822
import SixD3RootB2569822
import SixD3RootA2599822
import SixD3RootB2599822
import SixD3RootA2899822
import SixD3RootB2899822
import SixD3RootA3569822
import SixD3RootB3569822
import SixD3RootA3599822
import SixD3RootB3599822
import SixD3RootA3679822
import SixD3RootB3679822
import SixD3RootA4569822
import SixD3RootB4569822
import SixD3RootA4679822
import SixD3RootB4679822
import SixD3RootA4789822
import SixD3RootB4789822
namespace Research.Graph9822.ThreeDirect
private def Covers (ds : List Dir) := ∀ {d}, d∈ds → (¬Nonempty (Rooms d false)) ∧ ¬Nonempty (Shared d)
private theorem coverCons {ds : List Dir} (d : Dir) (B : ¬Nonempty (Rooms d false))
    (A : ¬Nonempty (Shared d)) (rest : Covers ds) : Covers (d::ds) := by
  intro q h
  rcases List.mem_cons.mp h with rfl|h
  · exact ⟨B,A⟩
  · exact rest h
private theorem emptyCover : Covers [] := by
  intro d h
  exact False.elim (List.not_mem_nil h)
theorem closedBoth {d : Dir} (h : d ∈ Research.SixD3.Labels.roster38) :
    (¬ Nonempty (Rooms d false)) ∧ ¬ Nonempty (Shared d) := by
  have all : Covers Research.SixD3.Labels.roster38 :=
    coverCons (0,1,3) B013.closed A013.closed (
    coverCons (0,1,7) B017.closed A017.closed (
    coverCons (0,1,8) B018.closed A018.closed (
    coverCons (0,1,9) B019.closed A019.closed (
    coverCons (0,2,3) B023.closed A023.closed (
    coverCons (0,2,6) B026.closed A026.closed (
    coverCons (0,2,8) B028.closed A028.closed (
    coverCons (0,2,9) B029.closed A029.closed (
    coverCons (0,3,6) B036.closed A036.closed (
    coverCons (0,3,7) B037.closed A037.closed (
    coverCons (0,3,9) B039.closed A039.closed (
    coverCons (0,6,7) B067.closed A067.closed (
    coverCons (0,7,8) B078.closed A078.closed (
    coverCons (0,8,9) B089.closed A089.closed (
    coverCons (1,3,5) B135.closed A135.closed (
    coverCons (1,3,7) B137.closed A137.closed (
    coverCons (1,3,9) B139.closed A139.closed (
    coverCons (1,4,5) B145.closed A145.closed (
    coverCons (1,4,7) B147.closed A147.closed (
    coverCons (1,4,8) B148.closed A148.closed (
    coverCons (1,5,9) B159.closed A159.closed (
    coverCons (1,7,8) B178.closed A178.closed (
    coverCons (1,8,9) B189.closed A189.closed (
    coverCons (2,3,5) B235.closed A235.closed (
    coverCons (2,3,6) B236.closed A236.closed (
    coverCons (2,3,9) B239.closed A239.closed (
    coverCons (2,4,5) B245.closed A245.closed (
    coverCons (2,4,6) B246.closed A246.closed (
    coverCons (2,4,8) B248.closed A248.closed (
    coverCons (2,5,6) B256.closed A256.closed (
    coverCons (2,5,9) B259.closed A259.closed (
    coverCons (2,8,9) B289.closed A289.closed (
    coverCons (3,5,6) B356.closed A356.closed (
    coverCons (3,5,9) B359.closed A359.closed (
    coverCons (3,6,7) B367.closed A367.closed (
    coverCons (4,5,6) B456.closed A456.closed (
    coverCons (4,6,7) B467.closed A467.closed (
    coverCons (4,7,8) B478.closed A478.closed (
    emptyCover))))))))))))))))))))))))))))))))))))))
  exact all h
end Research.Graph9822.ThreeDirect
#print axioms Research.Graph9822.ThreeDirect.closedBoth
