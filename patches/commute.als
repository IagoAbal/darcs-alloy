
module patches/commute

/**
	Commutation of patches.

	This code tries to reproduce Darcs commutation strategy for primitive patches.
	The number of possible combinations for commute is quite high, but there is
	only a small number of essential cases such that any other can be based on them.

	Darcs uses some clever tricks to reduce the amount of code  as possible. 
	* One of these tricks is to test commuting against classes of patches before test against
	  concrete patches.
	* Another trick is based on patch inversion and the symmetry of commutation, 
	  but this trick is not necessary a good idea in Alloy since given Commute[p,q,q',p']
	the inverses of p, q, q' and p' are required to exist, but this is not guaranteed unless we
	force this as a fact.
	(See Darcs.Patch.Prim' cleverCommute internal function.)

	Note the same limitations for manipulating paths that forced us to restrict Rename
	operation for tree also apply here.

	See http://hackage.haskell.org/packages/archive/darcs/2.5/doc/html/src/Darcs-Patch-Prim.html
*/


open tree
open patches/types
open patches/apply
open patches/invert



//////// Commute

pred Commute[p, q, q', p' : Patch] {
		 CommuteDirpatches[p,q,q',p']
	or CommuteFilepatches[p,q,q',p']
	or CommuteDirAndFilePatches[p,q,q',p']
	or CommuteMovePatches[p,q,q',p']
	or CommuteMoveAndDirFilePatches[p,q,q',p']
}

--- > Consistency & safety

pred Commute_Consistent[p, q, q', p' : Patch] {
	p.Inv and q.Inv
	Commute[p,q,q',p']
}
run Commute_Consistent for 5 but exactly 3 Patch, 4 seq

assert Commute_Safe {
	all p, q, q', p' : Patch |
		p.Inv and q.Inv and Commute[p,q,q',p'] => q'.Inv and p'.Inv
}
check Commute_Safe for 5

//////// Commute //////// Properties

-- Can't be verified with Alloy: universe is not saturated enough
//assert Commute_Sequential { 
//	all p, q, q', p' : Patch |
//		p.Inv and q.Inv and Commute[p,q,q',p'] => sequential[q',p']
//}
//check Commute_Sequential

assert Commute_Simple {
	all p, q, q', q'', p', p'' : Patch |
		(p.Inv and q.Inv and
			Commute[p,q,q',p'] and Commute[p,q,q'',p'']) => (p'' = p' and q'' = q')
}
check Commute_Simple for 5 but 6 Patch

assert Commute_Injective {
	all p, q, r, s, q', p' : Patch |
		(p.Inv and q.Inv and r.Inv and s.Inv and
			Commute[p,q,q',p'] and Commute[r,s,q',p']) => (p = r and q = s)
}
check Commute_Injective for 5 but 6 Patch

-- Can't be verified with Alloy: universe is not saturated enough
//assert Commute_Symmetric {
//	all p, q, q', p' : Patch | Commute[p,q,q',p'] => Commute[q',p',p,q]
//}

assert Commute_Symmetric_Weak {
	all p, q, q', p' : Patch | 
			Commute[p,q,q',p'] and sequential[q',p'] => Commute[q',p',p,q]
}
check Commute_Symmetric_Weak for 4

-- Can't be verified with Alloy: universe is not saturated enough
//assert Commute_EffectPreserving {
//	all p, q, q', p' : Patch |
//		(p.Inv and q.Inv and 
//			Commute[p,q,q',p']) => ((p.Effect) . (q.Effect)) = ((q'.Effect) . (p'.Effect))
//} 

assert Commute_EffectPreserving_Left_Weak {
	all p, q, q', p' : Patch, t1, t2, t2', t3 : Tree |
			(p.Inv and q.Inv and t1.Inv and
				Apply[t1,p,t2] and Apply[t2,q,t3] and Apply[t1,q',t2'] and
				Commute[p,q,q',p']) => Apply[t2',p',t3]
}
check Commute_EffectPreserving_Left_Weak for 4

-- Can't be verified in Alloy
//assert Commute_Rotating {
//	all p, q, q', p', q'_inv, q_inv : Patch | 
//		(q.Invert[q_inv] and q'.Invert[q'_inv] and
//			Commute[p,q,q',p']) => Commute[q'_inv,p,p',q_inv]
//}

assert Commute_Rotating_Weak {
	all p, q, q', p', q'_inv, q_inv : Patch | 
		(q.Invert[q_inv] and q'.Invert[q'_inv] and sequential[q'_inv,p] and
					Commute[p,q,q',p']) => Commute[q'_inv,p,p',q_inv]
}
check Commute_Rotating_Weak for 4

assert Commute_Permutivity {
	all x, x1,x3,x3',x4,y,y1,y2,y2',y4,z,z2,z3,z3',z4 : Patch |
			(Commute[x,y,y1,x1] and Commute[x1,z,z4,x4] and Commute[y1,z4,z3',y4] 
			and Commute[y,z,z2,y2] and Commute[x,z2,z3,x3]
			and Commute[y4,x4,x3',y2'])
			=>
			(z3' = z3 and y2' = y2 and x3' = x3)
}

check Commute_Permutivity for 4 but 15 Patch

//////// Commute //////// Dir patch

pred CommuteDirpatches[dp1, dp2, dp2', dp1' : DirPatch] {
	-- PRE
	dp1 in DirPatch and dp2 in DirPatch and dp2' in DirPatch and dp1' in DirPatch
	sequential[dp1,dp2]
	not isPrefix[dp1.path, dp2.path]
	not isPrefix[dp2.path, dp1.path]
--	dp1.path != dp2.path	// unuseful code from Darcs, conditions above suffices

	dp2' = dp2
	dp1' = dp1
}

run CommuteDirpatches for 4 // Consistency

//////// Commute //////// File patch

pred CommuteFilepatches[fp1, fp2, fp2', fp1' : FilePatch] {
	-- PRE
	fp1 in FilePatch and fp2 in FilePatch and fp2' in FilePatch and fp1' in FilePatch
	sequential[fp1,fp2]
	
	fp1.path != fp2.path 
		=> fp2' = fp2 and fp1' = fp1		// trivially commute
		else CommuteSFHunks[fp1,fp2,fp2',fp1']
}

--- > Consistency & safety

pred CommuteFilepatches_Consistent[fp1, fp2, fp2', fp1' : FilePatch] {
	fp1.Inv and fp2.Inv
	CommuteFilepatches[fp1,fp2,fp2',fp1']
}
run CommuteFilepatches_Consistent for 4

assert CommuteFilepatches_Safe {
	all fp1, fp2, fp2', fp1' : FilePatch |
		(fp1.Inv and fp2.Inv and CommuteFilepatches[fp1,fp2,fp2',fp1']) => (fp2'.Inv and fp1'.Inv)
}
check CommuteFilepatches_Safe for 4

//////// Commute //////// File patch //////// Hunk

// Commutation of a pair of hunks that modify the same file.
// See Darcs.Patch.Prim commuteHunk internal function.
pred CommuteSFHunks[h1, h2, h2', h1' : Hunk] {
	-- PRE
	h1 in Hunk and h2 in Hunk and h2' in Hunk and h1' in Hunk
	h1.path = h2.path		// the h1.path!=h2.path case is handled for file-patches at once
 	sequential[h1,h2]

	-- CHANGE
	h1.line.add[#h1.new] < h2.line
			=> (HunkInv[h2.line.sub[h1.ldelta],h2.old,h2.new] and
					h2'.line = h2.line.sub[h1.ldelta] and h1'.line = h1.line)
	else h2.line.add[#h2.old] < h1.line 
			=> (HunkInv[h1.line.add[h2.ldelta],h1.old,h1.new] and
					h2'.line = h2.line and h1'.line = h1.line.add[h2.ldelta])
	else (h1.line.add[#h1.new] = h2.line and h1.isReplaceHunk and h2.isReplaceHunk)
			=> (HunkInv[h2.line.sub[h1.ldelta],h2.old,h2.new] and
					h2'.line = h2.line.sub[h1.ldelta] and h1'.line = h1.line)
	else (h2.line.add[#h2.old] = h1.line and h1.isReplaceHunk and h2.isReplaceHunk
			and HunkInv[h1.line.add[h2.ldelta],h1.old,h1.new] and
					h2'.line = h2.line and h1'.line = h1.line.add[h2.ldelta])

	-- KEEP
	h2'.path = h2.path
	h2'.old = h2.old
	h2'.new = h2.new
	h1'.path = h1.path
	h1'.old = h1.old
	h1'.new = h1.new
}

--- > Consistency & safety

pred CommuteSFHunks_Consistent[h1, h2, h2', h1' : Hunk] {
	h1.HunkInv and h2.HunkInv
	CommuteSFHunks[h1,h2,h2',h1' ] 
}
run CommuteSFHunks_Consistent for 5 but exactly 3 Patch, 3 seq

pred CommuteSFHunks_Consistent_Case3[h1, h2, h2', h1' : Hunk] {
	h1.HunkInv and h2.HunkInv
	h1.line.add[#h1.new] = h2.line
	h2' != h2 or h1' != h1
	CommuteSFHunks[h1,h2,h2',h1' ]
}
run CommuteSFHunks_Consistent_Case3 for 5 but exactly 3 Patch, 3 seq

pred CommuteSFHunks_Consistent_Case4[h1, h2, h2', h1' : Hunk] {
	h1.HunkInv and h2.HunkInv
	h1.line.add[#h1.new] != h2.line and h2.line.add[#h2.old] = h1.line
	h2' != h2 or h1' != h1
	CommuteSFHunks[h1,h2,h2',h1'] 
}
run CommuteSFHunks_Consistent_Case4 for 5 but exactly 3 Patch, 3 seq

assert CommuteSFHunk_Safe {
	all h1, h2, h2', h1' : Hunk |
		(h1.Inv and h2.Inv and CommuteSFHunks[h1,h2,h2',h1']) => (h2'.Inv and h1'.Inv)
}
check CommuteSFHunk_Safe for 5 but 4 Patch

//////// Commute //////// Dir & File patches

pred CommuteDirAndFilePatches[p, q, q', p' : Patch] {
	CommuteFilepatchDirpatch[p,q,q',p'] or CommuteDirpatchFilepatch[p,q,q',p']
}

pred CommuteFilepatchDirpatch[fp : FilePatch, dp, dp' : DirPatch, fp' : FilePatch] {
	-- PRE
	fp in FilePatch and dp in DirPatch and dp' in DirPatch and fp' in FilePatch
	sequential[fp,dp]
	not isPrefix[dp.path, fp.path]

	dp' = dp
	fp' = fp
}

pred CommuteDirpatchFilepatch[dp : DirPatch, fp, fp' : FilePatch,  dp' : DirPatch] {
	-- PRE
	dp in DirPatch and fp in FilePatch and fp' in FilePatch and dp' in DirPatch
	sequential[dp,fp]
	not isPrefix[dp.path,fp.path]

	dp' = dp
	fp' = fp
}

--- > Consistency & safety

pred CommuteFilepatchDirpatch_Consistent[p, q, q', p' : Patch] {
	p.Inv and q.Inv
	CommuteFilepatchDirpatch[p,q,q',p']
}
run CommuteFilepatchDirpatch_Consistent for 4

pred CommuteDirpatchFilepatch_Consistent[p, q, q', p' : Patch] {
	p.Inv and q.Inv
	CommuteDirpatchFilepatch[p,q,q',p']
}
run CommuteDirpatchFilepatch_Consistent for 4

assert CommuteDirAndFilePatches_Safe {
	all p, q, q', p' : Patch |
		(p.Inv and q.Inv and CommuteDirAndFilePatches[p,q,q',p']) => (q'.Inv and p'.Inv)
}
check CommuteDirAndFilePatches_Safe for 5

//////// Commute //////// Move
--
-- When Move patches are involved commutation could require
-- manipulating paths in a way we don't know how to do in Alloy due to the
-- lack of recursion. So, as we did for tree module, we have restricted commutation
-- for cases in which only the direct parent of a path could be changed.
--
-- This restriction is also needed due to the restrictions imposed to Rename operation
-- on trees, in order to ensure that commute preserves sequential property.
-- Consider we were able to commute 
--                 (Move /foo /bar,Adddir /bar/1/a) <-> (Adddir /foo/1/a, Move /foo /bar)
-- clearly (Adddir /foo/1/a . Move /foo /bar) is not sequential because any tree resulting
-- from applying path 'Adddir /foo/1/a' violates Rename preconditions.
--

pred CommuteMovePatches[mv1, mv2, mv2', mv1': Move] {
	-- PRE
	mv1 in Move and mv2 in Move and mv2' in Move and mv1' in Move
	sequential[mv1,mv2]
	mv2.source != mv1.dest
	mv2.dest != mv1.source
	-- Example: /1/a -> /2 ; /1 -> /2/b
	-- We cannot commute both patches because the second requires /2 to exist, but it only exists
	-- after the first patch is applied.
	not (isPrefix[mv2.source,mv1.source] or isPrefix[mv1.dest,mv2.dest])
	-- Restriction forced due to limited path manipulation.
	-- Example /foo -> /bar ; /bar/1/a -> /baz
	(mv2.source not in mv1.dest.parent.ancestor) or (mv1.dest not in mv2.source.parent.ancestor)

	mv1.dest = mv2.source.parent 
		=>(mv2'.source.parent = mv1.source and mv2'.source.name = mv2.source.name and mv2'.dest = mv2.dest)
		else mv2' = mv2
	mv2.source = mv1.dest.parent
		=> (mv1'.source = mv1.source and mv1'.dest.parent = mv2.dest and mv1'.dest.name = mv1.dest.name)
		else mv1' = mv1
}

-- > Consistency & safety

pred CommuteMovePatches_Consistent[mv1, mv2, mv2', mv1': Move] {
	mv1.Inv and mv2.Inv
	CommuteMovePatches[mv1,mv2,mv2',mv1']
}
run CommuteMovePatches_Consistent for 6 but 4 Patch

assert CommuteMovePatches_Safe {
	all mv1, mv2, mv2', mv1': Move |
		(mv1.MoveInv and mv2.MoveInv and CommuteMovePatches[mv1,mv2,mv2',mv1'])
			=> (mv2'.MoveInv and mv1'.MoveInv)
}
check CommuteMovePatches_Safe for 5

--- > Move & Dir/File patches

pred CommuteMoveAndDirFilePatches[p, q, q', p' : Patch] {
	CommuteMoveAndDirPatches[p,q,q',p'] or CommuteMoveAndFilePatches[p,q,q',p']
}

//////// Commute //////// Move & Dir patches

pred CommuteMoveAndDirPatches[p, q, q', p' : Patch] {
	CommuteDirpatchMove[p,q,q',p'] or CommuteMoveDirpatch[p,q,q',p']
}

pred CommuteDirpatchMove[dp : DirPatch, mv, mv' : Move, dp' : DirPatch] {
	-- PRE
	dp in DirPatch and mv in Move and mv' in Move and dp' in DirPatch
	(dp in Adddir and dp' in Adddir) or (dp in Rmdir and dp' in Rmdir)
	sequential[dp,mv]
	not (isPrefix[dp.path,mv.source] or isPrefix[dp.path,mv.dest])
	mv.source != dp.path
	-- Restriction forced due to limited path manipulation.
	-- Example: Dp /foo/1/a ; /foo -> /bar
	mv.source not in dp.path.parent.ancestor

	mv' = mv
	mv.source = dp.path.parent =>(dp'.path.parent = mv.dest and dp'.path.name = dp.path.name)
		else	dp' = dp
}

pred CommuteMoveDirpatch[mv : Move, dp, dp' : DirPatch, mv' : Move] {
	-- PRE
	mv in Move and dp in DirPatch and dp' in DirPatch and mv' in Move
	(dp in Adddir and dp' in Adddir) or (dp in Rmdir and dp' in Rmdir)
	sequential[mv,dp]
	not (isPrefix[dp.path,mv.source] or isPrefix[dp.path,mv.dest])
	-- Restriction forced due to limited path manipulation.
	-- Example: /foo -> /bar ; Dp /bar/1/a
	mv.dest not in dp.path.parent.ancestor

	mv.dest = dp.path.parent => (dp'.path.parent = mv.source and dp'.path.name = dp.path.name)
		else dp' = dp
	mv' = mv
}

--- > Consistency & safety

pred CommuteDirpatchMove_Consistent[dp : DirPatch, mv, mv' : Move, dp' : DirPatch] {
	mv.Inv
	CommuteDirpatchMove[dp,mv,mv',dp']
}
run CommuteDirpatchMove_Consistent for 5 but 4 Patch

pred CommuteMoveDirpatch_Consistent[mv : Move, dp, dp' : DirPatch, mv' : Move] {
	mv.Inv
	CommuteMoveDirpatch[mv,dp,dp',mv']
}
run CommuteMoveDirpatch_Consistent for 5 but 4 Patch

assert CommuteMoveAndDirPatches_Safe {
	all p, q, q', p' : Patch |
		(p.Inv and q.Inv and CommuteMoveAndDirPatches[p,q,q',p']) => (q'.Inv and p'.Inv)
}
check CommuteMoveAndDirPatches_Safe for 5

//////// Commute //////// Move & File patches

pred CommuteMoveAndFilePatches[p, q, q', p' : Patch] {
	CommuteFilepatchMove[p,q,q',p'] or CommuteMoveFilepatch[p,q,q',p']
}

pred CommuteFilepatchMove[fp : FilePatch, mv, mv' : Move, fp' : FilePatch] {
	-- PRE
	mv in Move and mv' in Move
	(fp in Hunk and fp' in Hunk) or (fp in Addfile and fp' in Addfile) or (fp in Rmfile and fp' in Rmfile)
	sequential[fp, mv]
	fp in Addfile => fp.path != mv.source
	fp in Rmfile => fp.path != mv.dest
	-- Restriction forced due to limited path manipulation.
	-- Example: Fp /foo/1/a ; /foo -> /bar
	mv.source not in fp.path.parent.ancestor
	
	mv' = mv
	fp.path = mv.source => fp'.path = mv.dest 
		else fp.path.parent = mv.source => (fp'.path.parent = mv.dest and fp'.path.name = fp.path.name)
		else fp'.path = fp.path
	fp in Hunk => fp'.line = fp.line and fp'.old = fp.old and fp'.new = fp.new
}

pred CommuteMoveFilepatch[mv : Move, fp, fp' : FilePatch, mv' : Move] {
	-- PRE
	mv in Move and mv' in Move
	(fp in Hunk and fp' in Hunk) or (fp in Addfile and fp' in Addfile) or (fp in Rmfile and fp' in Rmfile)
	sequential[mv, fp]
	fp in Addfile => fp.path != mv.source
	fp in Rmfile => fp.path != mv.dest
	-- Restriction forced due to limited path manipulation.
	-- Example: /foo -> /bar ; Fp /bar/1/a
	mv.dest not in fp.path.parent.ancestor
	
	fp.path = mv.dest => fp'.path = mv.source 
		else fp.path.parent = mv.dest => (fp'.path.parent = mv.source and fp'.path.name = fp.path.name)
		else fp'.path = fp.path
	fp in Hunk => fp'.line = fp.line and fp'.old = fp.old and fp'.new = fp.new
	mv' = mv
}

--- > Consistency & safety

pred CommuteFilepatchMove_Consistent[fp : FilePatch, mv, mv' : Move, fp' : FilePatch] {
	fp.Inv and mv.Inv
	CommuteFilepatchMove[fp,mv,mv',fp']
}
run CommuteFilepatchMove_Consistent for 5 but 4 Patch

pred CommuteMoveFilepatch_Consistent[mv : Move, fp, fp' : FilePatch, mv' : Move] {
	mv.MoveInv and fp.Inv
	CommuteMoveFilepatch[mv,fp,fp',mv']
}
run CommuteMoveFilepatch_Consistent for 5 but 4 Patch

assert CommuteMoveAndFilePatches {
	all p, q, q', p' : Patch |
		(p.Inv and q.Inv and CommuteMoveAndFilePatches[p,q,q',p']) => (q'.Inv and p'.Inv)
}
check CommuteMoveAndFilePatches for 5

