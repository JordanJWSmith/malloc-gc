|| DEFINE DATA STRUCTURES

|| address is an integer representing the block's starting position on the heap
address == num

|| liveness determines whether the block is in use or free
liveness ::= Free | Live

|| size is integer representing the total size of the block
size == num

|| markbit is integer - 0 for unmarked and 1 for marked
markbit == num

|| blocks contain their address, their liveness bit and their size
block == (address, liveness, size)

|| heap is recursive list of blocks
heap ::= HEmpty | Cons block heap

|| freelist is list of tuples - addresses act as pointers to the heap
flist == [(address, size)]

|| marklist is a list of tuples - addresses act as pointers to the heap
mlist == [(address, markbit)]

|| rootnodes is a list of num
rnodes == [address]

||define size of heap - increase this to increase amount of memory
heapsize :: num
heapsize = 120

|| tree of nodes for use in mark-scan
roottree * ::= REmpty | RNode * [roottree *]



|| FUNCTIONS

|| given a heap, create a freelist
freelist :: heap -> flist
freelist HEmpty = []
freelist (Cons (a, l, s) h) = (a, s) : (freelist h), if (l == Free)
                            = (freelist h)         , otherwise


|| given a heap, block size and address, add a new live block to the heap (split a free block to make room)
|| this model follows an address-ordered first-fit policy
splitblock :: heap -> size -> address -> heap
splitblock HEmpty n p		  = error "unable to allocate memory"
splitblock (Cons (a, l, s) h) n p = (Cons (a, Live, n) (Cons (a+n, Free, s-n) h)), if (a == p) & (l == Free) & (a+n <= heapsize) & (s-n > 0)
				  = (Cons (a, Live, n) h)			 , if (a == p) & (l == Free) & (a+n <= heapsize) & (s-n <= 0)
				  = (Cons (a, l, s) (splitblock h n p))          , otherwise


|| given a heap and an address, turn a live block into a free block
free :: heap -> address -> heap
free HEmpty p = error "no such block"
free (Cons (a, l, s) h) p = (Cons (a, Free, s) h)      , if (l == Live) & (a == p)
			  = (Cons (a, l, s) (free h p)), otherwise


|| given a freelist and a size, return a suitable address
|| if there is no suitable address, return negative int
malloc :: flist -> size -> address
malloc [] n     = -1
malloc (a:as) n = fst a, if ((snd a) >= n)
		= malloc (as) n, otherwise



|| given a heap, merge contiguous free blocks
freemerge :: heap -> heap
freemerge (Cons (a, l, s) HEmpty)                   = (Cons (a, l, s) HEmpty)
freemerge (Cons (a, Free, s) (Cons (b, Free, t) h)) = (freemerge (Cons (a, Free, s+t) h))
freemerge (Cons (a, l, s) (Cons (b, m, t) h))       = (Cons (a, l, s) (freemerge (Cons (b, m, t) h)))



|| given a heap, initialise a list where each block's markbit is zero
marklist :: heap -> mlist
marklist HEmpty 	    = []
marklist (Cons (a, l, s) h) = (a, 0) : (marklist h), if (l == Live)
			    = (marklist h)	   , otherwise


|| given an address and a set of root nodes, test membership of the address in rootnodes
comp :: address -> rnodes -> bool
comp b []     = False
comp b (a:as) = True     , if (b == a)
	      = comp b as, otherwise


|| given a marklist [(address, 0)] and a set of live block addresses, change markbit to 1 if address is a member of set
mark :: mlist -> rnodes -> mlist
mark (b:bs) [] 	   = (b:bs)
mark [] (a:as)     = []
mark (b:bs) (a:as) = ((fst b), 1) : (mark bs (a:as)), if (comp (fst b) (a:as))
		   = b : (mark bs (a:as)), otherwise


|| given a completed marklist and a heap, convert the unmarked addresses to free
sweep :: heap -> mlist -> heap
sweep HEmpty [] 		= HEmpty
sweep HEmpty (b:bs) 		= HEmpty
sweep (Cons (a, l, s) h) [] 	= (Cons (a, l, s) h)
sweep (Cons (a, l, s) h) (b:bs) = free (Cons (a, l, s) (sweep h bs)) (fst b), if ((snd b) == 0)
				= (Cons (a, l, s) (sweep h bs))		      , otherwise



|| given a heap, perform mark-scan and return the new heap
markscan :: heap -> heap
markscan h = freemerge (sweep h (mark (marklist h) (rootset blocktree roots)))


|| create a stack of values in a tree
markstack :: roottree num -> rnodes
markstack REmpty           = []
markstack (RNode a (l:ls)) = (a : map val ls) ++ (markstack l)
                             where
                             val (RNode a (l:ls)) = a


|| given a tree of connected nodes and a set of root nodes, return a stack of the root nodes and their children
rootset :: roottree num -> rnodes -> rnodes
rootset r [] = []
rootset r (n:ns) = (subtree r n) ++ (rootset r ns)
		   where
		   subtree REmpty s = markstack REmpty
		   subtree (RNode a l) s = markstack (RNode a l), if (s == a)
		   subtree (RNode a (l:ls)) s = markstack (RNode a (l:ls)), if (s == a)
		   			      = (subtree l s), if (ls == [])
                           		      = (subtree l s) ++ (subtree (hd ls) s), otherwise


|| given a heap and a block size, insert the new block into the heap
|| if there is no suitable memory left in the heap, perform mark-scan garbage collection and re-allocate the block
|| for requested size n, malloc looks for a free block with size m such that m >= X + (max (n,4)).
|| here, header size X = 4
insert :: heap -> size -> heap
insert h n = error "requested block larger than heap size", if (n > heapsize)
insert h n = (splitblock h (m+4) (malloc (freelist h) (m+4))), if ((malloc (freelist h) (m+4)) > 0)
	   = splitblock u (m+4) (malloc (freelist u) (m+4)), otherwise
	     where
	     u = markscan h
	     m = max[n, 4]


|| SAMPLE DATA

|| a graph to demonstrate how live blocks are connected via pointers
|| feel free to experiment by adding more addresses to the graph
r1 = RNode 0 [r2, r3]
r2 = RNode 24 [r4, r5]
r3 = RNode 36 [r6]
r4 = RNode 52 [REmpty]
r5 = RNode 100 [REmpty]
r6 = RNode 88 [REmpty]

|| representing the graph of connected live blocks
blocktree :: roottree num
blocktree = r1

|| a set of root addresses
|| feel free to experiment by including different root addresses in the set
roots :: rnodes
roots = [24, 36]


|| The following is a set of sample data designed to walk through the memory allocation and garbage collection process.
|| Feel free to experiment with different block sizes and heap sizes.
|| This model uses an address-ordered first fit policy.
|| The free block with the lowest address is considered first for allocation.
|| This clusters live memory blocks at the lower end of memory and is better for virtual memory performance.
|| However, first fit policies may eventually degrade performance due to many small blocks clustering at the start of the free list.
|| This model combats this by coalescing contiguous free blocks.


|| initialise empty heap - this is one large free block with size=heapsize
initheap :: heap
initheap = Cons (0, Free, heapsize) HEmpty

|| Add a block to empty heap
b1 :: heap
b1 = insert initheap 4          || Cons (0,Live,8) (Cons (8,Free,112) HEmpty)

|| Add another block
b2 :: heap
b2 = insert b1 12               || Cons (0,Live,8) (Cons (8,Live,16) (Cons (24,Free,96) HEmpty))

|| Add another block
b3 :: heap
b3 = insert b2 8                || Cons (0,Live,8) (Cons (8,Live,16) (Cons (24,Live,12) (Cons (36,Free,84) HEmpty)))

|| Add another block
b4 :: heap
b4 = insert b3 4                || Cons (0,Live,8) (Cons (8,Live,16) (Cons (24,Live,12) (Cons (36,Live,8) (Cons (44,Free,76) HEmpty))))

|| Add another block
b5 :: heap
b5 = insert b4 4                || Cons (0,Live,8) (Cons (8,Live,16) (Cons (24,Live,12) (Cons (36,Live,8) (Cons (44,Live,8) (Cons (52,Free,68) HEmpty)))))

|| Add another block
b6 :: heap
b6 = insert b5 12               || Cons (0,Live,8) (Cons (8,Live,16) (Cons (24,Live,12) (Cons (36,Live,8) (Cons (44,Live,8) (Cons (52,Live,16) (Cons (68,Free,52) HEmpty))))))

|| Add another block
b7 :: heap
b7 = insert b6 8                || Cons (0,Live,8) (Cons (8,Live,16) (Cons (24,Live,12) (Cons (36,Live,8) (Cons (44,Live,8) (Cons (52,Live,16) (Cons (68,Live,12) (Cons (80,Free,40) HEmpty)))))))

|| Add another block
b8 :: heap
b8 = insert b7 4                || Cons (0,Live,8) (Cons (8,Live,16) (Cons (24,Live,12) (Cons (36,Live,8) (Cons (44,Live,8) (Cons (52,Live,16) (Cons (68,Live,12) (Cons (80,Live,8) (Cons (88,Free,32) HEmpty))))))))

|| Add another block
b9 :: heap
b9 = insert b8 8                || Cons (0,Live,8) (Cons (8,Live,16) (Cons (24,Live,12) (Cons (36,Live,8) (Cons (44,Live,8) (Cons (52,Live,16) (Cons (68,Live,12) (Cons (80,Live,8) (Cons (88,Live,12) (Cons (100,Free,20) HEmpty)))))))))

|| Add another block (heap is now full)
b10 :: heap
b10 = insert b9 16              || Cons (0,Live,8) (Cons (8,Live,16) (Cons (24,Live,12) (Cons (36,Live,8) (Cons (44,Live,8) (Cons (52,Live,16) (Cons (68,Live,12) (Cons (80,Live,8) (Cons (88,Live,12) (Cons (100,Live,20) HEmpty)))))))))

|| Add another block (perform mark-scan garbage collection and insert the new block)
b11 :: heap
b11 = insert b10 20             || Cons (0,Live,24) (Cons (24,Live,12) (Cons (36,Live,8) (Cons (44,Free,8) (Cons (52,Live,16) (Cons (68,Free,20) (Cons (88,Live,12) (Cons (100,Live,20) HEmpty)))))))





|| Take a look at the 'insert' process in more detail

|| Look at the free list for the heap - it contains pointers to free blocks and their corresponding size
i1 :: flist
i1 = freelist b11 		|| [(44,8),(68,20)]

|| Use malloc to parse the freelist and return the address of a suitable block
i2 :: address
i2 = malloc i1 12		|| 68

|| Split (if new block size < free block size) or replace (if new block size == free block size) the free block to allocate the new block
i3 :: heap
i3 = splitblock b11 12 i2	|| Cons (0,Live,24) (Cons (24,Live,12) (Cons (36,Live,8) (Cons (44,Free,8) (Cons (52,Live,16) (Cons (68,Live,12) (Cons (80,Free,8) (Cons (88,Live,12) (Cons (100,Live,20) HEmpty))))))))





|| Take a look at the garbage collection process in more detail

|| Initialise markbits to 0
m1 :: mlist
m1 = marklist b10 	       || [(0,0),(8,0),(24,0),(36,0),(44,0),(52,0),(68,0),(80,0),(88,0),(100,0)]

|| Parse the root nodes and their pointers to create the mark stack
m2 :: rnodes
m2 = rootset blocktree roots   || [24,100,52,36,88]

|| Addresses reachable from the rootset are marked 1
m3 :: mlist
m3 = mark m1 m2		       || [(0,0),(8,0),(24,1),(36,1),(44,0),(52,1),(68,0),(80,0),(88,1),(100,1)]

|| Convert the unmarked addresses in the heap to free blocks
s1 :: heap
s1 = sweep b10 m3	       || Cons (0,Free,8) (Cons (8,Free,16) (Cons (24,Live,12) (Cons (36,Live,8) (Cons (44,Free,8) (Cons (52,Live,16) (Cons (68,Free,12) (Cons (80,Free,8) (Cons (88,Live,12) (Cons (100,Live,20) HEmpty)))))))))

|| Merge contiguous free blocks
c1 :: heap
c1 = freemerge s1              || (0,Free,24) (Cons (24,Live,12) (Cons (36,Live,8) (Cons (44,Free,8) (Cons (52,Live,16) (Cons (68,Free,20) (Cons (88,Live,12) (Cons (100,Live,20) HEmpty)))))))

|| Combine the above five steps to return an updated heap, ready for inserting the next block (b11)
u1 :: heap
u1 = markscan b10	       || Cons (0,Free,24) (Cons (24,Live,12) (Cons (36,Live,8) (Cons (44,Free,8) (Cons (52,Live,16) (Cons (68,Free,20) (Cons (88,Live,12) (Cons (100,Live,20) HEmpty)))))))
