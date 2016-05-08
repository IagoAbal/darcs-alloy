
module patches/check_generator

/**
	This module uses generator axioms to force a saturated universe
	in which we could properly check some assertions (mainly about commute).
*/


open tree
open patches/types
open patches/commute



--
-- A small saturated universe of trees is forced.
--
-- We only consider trees with just one file, which has all possible contents,
-- so this saturated universe is mainly useful to verify things about hunks.
-- Attempts to generate bigger universes in order to cover more kind of patches
-- were abandoned due to the explosion of the number of variables and clauses,
-- and very large execution times.
--
fact {
	all t:Tree, f : Path | #t.content[f] <= 3
	one t : Tree | t.Inv and t.isEmpty
	all f : Path | some t : Tree | 
			t.Inv and no t.Dirs and t.Files = f and no t.content[f]
	all f : Path, l : Line | some t : Tree | 
			t.Inv and one t.Items and t.content[f] = (0 -> l)
	all f : Path, l1, l2 : Line | some t : Tree |
	 	t.Inv and one t.Items and t.content[f] = (0 -> l1) + (1 -> l2)
	all f : Path, l1, l2, l3: Line | some t : Tree | 
		t.Inv and one t.Items and t.content[f] = (0 -> l1) + (1 -> l2) + (2 -> l3)
}
			-- 1 Path, 2 Line, max_file_size = 3
			-- 1 + (2^0 + 2^1 + 2^2 + 2^3) = 16
run {} for 16 but exactly 1 Path, exactly 2 Line, 0 Patch



//////// Assertions //////// Commute (hunks)

assert Commute_Sequential { 
	all p, q, q', p' : Hunk |
		(p.Inv and q.Inv and Commute[p,q,q',p']) => sequential[q',p']
} 
check Commute_Sequential for 16 but 3 seq, exactly 1 Path, exactly 2 Line

-- This assertion is invalid due to filesystem limits
-- Example: If t1 file has exactly 3 lines, and q' is a hunk with ldelta >= 1, then
-- there is no t2' such that Apply[t1,q',t2'] because in our universe the file size
-- limit is 3.
assert Commute_EffectPreserving_Left {
	all p, q, q', p' : Hunk, t1, t2, t3 : Tree |
		(p.Inv and q.Inv and t1.Inv and
			Commute[p,q,q',p'] and Apply[t1,p,t2] and Apply[t2,q,t3])
				=> some t2' : Tree | Apply[t1,q',t2'] and Apply[t2',p',t3]
} 
check Commute_EffectPreserving_Left for 16 but 3 seq, exactly 1 Path, exactly 2 Line, 3 Patch

assert Commute_EffectPreserving_Left_Weak {
	all p, q, q', p' : Hunk, t1, t2, t2', t3 : Tree |
		(p.Inv and q.Inv and t1.Inv and
			Commute[p,q,q',p'] and Apply[t1,p,t2] and Apply[t2,q,t3] and Apply[t1,q',t2']) =>Apply[t2',p',t3]
} 
check Commute_EffectPreserving_Left_Weak for 16 but 3 seq, exactly 1 Path, exactly 2 Line, 3 Patch

assert Commute_Symmetric {
	all p, q, q', p' : Hunk | 
		(p.Inv and q.Inv and Commute[p,q,q',p']) => Commute[q',p',p,q]
}
check Commute_Symmetric for 16 but 3 seq, exactly 1 Path, exactly 2 Line

assert Commute_Rotating {
	all p, q, q', p', q'_inv, q_inv : Hunk | 
		(p.Inv and q.Inv and 
			Invert[q,q_inv] and Invert[q',q'_inv] and Commute[p,q,q',p']) => Commute[q'_inv,p,p',q_inv]
}
check Commute_Rotating for 16 but 3 seq, exactly 1 Path, exactly 2 Line
