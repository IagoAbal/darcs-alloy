
module patches/types

/**
	The hierarchy of patches types.

	Only fundamental patches are subject to modeling. 
	We have omitted both 'Change pref' and 'Token replace' patches because
	they are not interesting for our purpose -- many Darcs developers agree with us.
	For more details about patches types see http://darcs.net/manual/Theory_patches.html.
*/


open tree



//////// Patch
--
-- Patches are organized hierarchically.
-- There are three main classes of patches (File, Dir and Move patches) 
-- and a total of 6 concrete patches.
-- 
--  Patches are canonized, otherwise some operations won't be injective.
-- Canonization of patches is also convenient for clarity.
-- Note that canonization must be done over the leafs of the Patch hierarchy.
--

abstract sig Patch {}

pred Inv[p : Patch] {
	p in Hunk => p.HunkInv
	p in Move => p.MoveInv
}

run Inv for 4 but exactly 1 Patch

//////// Patch //////// Directory patch
-- 
-- Directory patches only take effect on a single directory.
-- We can add or remove a directory.
--

abstract sig DirPatch extends Patch {
	path : Path
}

-- Adddir creates a new empty directory.
-- Rmdir removes an *empty* directory.
sig Adddir, Rmdir extends DirPatch {}

fact CanonizeAdddir {
	no disj addd1, addd2 : Adddir | addd1.path = addd2.path
}

fact CanonizeRmdir {
	no disj rmd1, rmd2 : Rmdir | rmd1.path = rmd2.path
}

//////// Patch //////// File patch
-- 
-- File patches only take effect on a single file.
-- We could add, remove or edit a file.
--

abstract sig FilePatch extends Patch {
	path : Path
}

sig Addfile, Rmfile extends FilePatch {}

fact CanonizeAddfile {
	no disj addf1, addf2 : Addfile | addf1.path = addf2.path
}

fact CanonizeRmfile {
	no disj rm1,rm2 : Rmfile | rm1.path = rm2.path
}

//////// Patch //////// File patch //////// Hunk
--
-- Hunks allow file editing. 
-- A hunk points to a line of a text file and replaces a set of lines by a 
-- different set of lines. Either of these sets may be empty, which would 
-- mean a deletion or insertion of lines. 
--

sig Hunk extends FilePatch {
	line : Int,
	old : seq Line,
	new : seq Line
}

fact CanonizeHunks {
	no disj h1, h2 : Hunk | 
		h1.path = h2.path and h1.line = h2.line and h1.old = h2.old and h1.new = h2.new
}

--
-- Since we model the content of a file as a sequence of lines seq/Int,
-- which is the maximum length a sequence can have, represents the file
-- size limit supported by the filesystem.
-- We assume that this limit is always smaller than the biggest representable
-- integer. We just use integers in Alloy, which are guaranteed to be greater
-- than seq/Int, in C this is ensured by the size_t type which is an integer
-- type bigger enough to contain the size of the biggest object your
-- system can handle. In Haskell we may use CSize defined at Foreign.C.Types.
--
pred HunkInv[h : Hunk] {
	HunkInv[h.line,h.old,h.new]
}

run HunkInv { some h : Hunk | h.HunkInv } for 3 but exactly 1 Patch

-- This predicate is useful for internal use, as in patches/commute/CommuteSFHunks.
pred HunkInv[line : Int, old : seq Line, new : seq Line] {
	(some old) or (some new)	// otherwise hunks are senseless
	-- Hunk does not try to add/remove content out of file limits.
	-- This should ensure that any hunk is applicable to some tree.
	line in seq/Int
	old.lastIdx.add[line] in seq/Int
	new.lastIdx.add[line] in seq/Int
}

--- > Other related functions & definitions

--
-- ldelta expresses the file size variation caused by the modification.
-- e.g. if we remove one line but add three the file size will be increased by +2.
--
fun ldelta[h : Hunk] : Int {
	sub[#h.new,#h.old]
}

pred isReplaceHunk[h : Hunk] {
	some h.old
	some h.new
}

run isReplaceHunk for 3 but 1 Patch, 1 Tree

////////  Patch ////////  Move patch
--
-- A move patch changes an item's path.
--

sig Move extends Patch {
	source : Path,
	dest : Path
} 

fact CanonizeMove {
	no disj mv1,mv2 : Move | mv1.source = mv2.source and mv1.dest = mv2.dest
}

pred MoveInv[mv : Move] {
	-- A move patch must be sensible (i.e. applicable to some tree).
	not isPrefix[mv.source, mv.dest]
	not isPrefix[mv.dest, mv.source]
}

run MoveInv for 4 but exactly 1 Patch
