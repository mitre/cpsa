# What we've done

1. We now have a program `cpsa4cmp` that can do isomorphism checks between the shapes in two different files. This doesn't current behave as it should. Expected behavior is described in the plan below. 

2. We have post-processing program `cpsa4subsume` that checks for homomorphisms between the shapes in a given file, organized by problem. If it finds a hom from x to y, then y is changed to have seen child x with a seen-ops field indication it was subsumed. This reads in a text file and outputs a text file. 

3. We have a compile-time flag in the main program `useGlobalShapes` that, when True, disables all generalization except for listener deletion, resulting in a search that has potentially many more realized skeletons at the leaves that aren't shapes. Those will be cleaned up by `cpsa4subsume`

4. We have used the above to find an issue in how isomorphism checking was done in the main code. It wasn't respecting the pov map everywhere. That has now been fixed with one caveat. In `Reduce.hs` the `solve` function calls `isomorphic` instead of `probIsomorphic`. At this point, we are comparing the input to the result of anything that needed to be done to make it into a skeleton. Neither has a `prob` yet. Using the old `isomorphic` is probably fine here. Silently ignore this issue for now. 

5. We also found an issue in how collapsing was working. It wasn't calling `withCoreFacts` which it should to get rid of extraneous facts added by rules before collapsing was applied. This has now been fixed. 

6. We have discovered a completeness bug in how augmentations work. The key example is `wonthull2.scm` in the test suite. There is a proposed fix in place which is to "deoriginate" a potential instance of a critical term at a potential transforming node. This is in `Cohort.hs` from around line 678 to line 732. This code seems to be doing the right thing, but there is a huge cost, at least on some examples. When generalization is turned off, it generates over 600 shape candidates that must be reduced by `cpsa4subsume`. With an O(n^2) cost, this has to do over 360,000 homomorphism checks, each of which is potentially expensive. We need another way. 

# Proposal

The proposal is reintroduce an earlier idea we had, and pair it with the post-processing program we already have. In particular, we can have `Reduce.hs` keep track of all the realized skeletons (after listener deletion) that are shape candidates. When a new shape candidate is found, if there is a homomorphism from an earlier shape candidate, we can detect it during the forward pass and already mark it has having a seen child, namely the one with a homomorphism to it. 

This is not sufficient to eliminate all extraneous candidates because sometimes it is the later candidate that is more general. Since the earlier candidate will have already been printed to a file, it doesn't make sense to try to rewrite it in place here. Thus the post-processing phase is still needed. However, there are several options to help improve the performance of post-processing. 

Option A is to only check homs from the lower to higher numbers in the forward search. Then when we get to post processing, we only have to look for homs from higher numbers to lower ones. 

Option B is to do the check from higher numbers to lower ones during the forward search too. Instead of rewriting the lower one now, we simply record the fact in a note. Then the note can be emitted at the end of the search tree as a comment. The post-processing phase can look for the note and add the seen child info to the skeletons according to the note. 

Option C is essentially the same as Option B, but instead of the post-processing being a separate program, it is folded into the main program as a final step. In this version, the intermediate writes serve only to help a user track progress and get information on partial runs. The final step would either write a new file, or obliterate the old one and write over it. Since we are already touching the main code, the benefit of a separate program is substantially diminished. 

Regardless of which option, I suggest we make the two possible paths (full generalization vs. global homomorphism check on shapes) a *runtime* toggle. It's currently a compile-time toggle. This has the immediate advantage of not having to rebuild when doing A/B testing. But it might also help users revert to the older, good-enough behavior in cases where the performance hit might be high. I would suggest the default path be through the new homchecking, and the presence of a runtime flag would be to turn on generalization.

Regarding the correct behavior of `cpsa4cmp`, the first difference is that it should work per-problem the way `cpsa4subsume` does. Secondly, it should be restructured so that we can keep track of which shape in one file was found to be isomorphic to which shape in the other. It can take advantage of the fact that isomorphisms are symmetric, so if there's an iso in one direction we know there's one in the other without have to check separately. It's still fair to assume that the problem sets are the same, but this should be noted in a comment. 

# Plan

1. Fix `cpsa4cmp` according to the description above.

2. Discuss the relative merits of options A, B, and C above, and help advise me on which one to go with.

3. Set up a clean stash of outputs that use the stock cpsa (with the iso and collapsing changes from above) for all .scm files in the test suite. 

4. Implement the homomorphism checking to occur during the search using whichever option I choose from step 2. This is where the runtime flag change will occur. Another detail I want to mention. Eventually I will want the homcheck path to emit (shape candidate) instead of (shape). However, the graph tooling currently relies on the (shape) field to know how to color things. So for now, keep emitting (shape) on both paths, but please make sure the writing of shapes branches according to this flag, and leave a comment so I know where I should change it to (shape candidate) later once I update the graph tooling. 

5. First verify that the full generalization path hasn't changed compared to the outputs from step 3. 

6. Now that we feel confident the generalization path implements the corrected stock cpsa, test the implementation from step 4 on a handful of core examples including ones we know to be problematic. We may need to debug at this point. Focus on correctness, and not performance, although feel free to note performance slowdowns. I think we still believe that the old path (full generalization) is correct on all files except for `dh-ca_hack.scm` (variable separation fails because it hits a limit), and `wonthull2.scm` (I think we know that 2 shapes is right, but it's much less certain). So correctness means that we find the same set of shapes with the new path as we do with the old path.

6. Once we feel good about correctness on the above examples, we need to do a comprehensive regression test on the full test suite. Start by testing only the .scm files in the test suite. Focus on correctness, but collect information about performance too (files with unexpectedly long runtimes, excessive increases in the number of skeletons explored between stock and new versions). Then when we feel good about those, we can test the .lsp files in the suite. Once all have been verified correct, we will start to address any performance issues. 