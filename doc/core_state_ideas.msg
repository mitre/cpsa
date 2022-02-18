From: "Joshua D. Guttman" <guttman@mitre.org>
To: "John D. Ramsdell" <ramsdell@mitre.org>
Cc: guttman@mitre.org (Joshua D. Guttman)
Subject: Re: Node pairs from the LeadsTo atomic formulas of a preskeleton 
Reply-To: guttman@mitre.org (Joshua D. Guttman)
Date: Wed, 03 Nov 2021 17:48:26 -0400
Message-ID: <m2h7csewr9.fsf@mitre.org>
--text follows this line--
John --

>   My claim is that CPSA3's implementation is
>   much more straightforward and understandable.

Hmm.  Maybe.  Of course, the CPSA 4 implementation
hasn't changed in over a year.

>   We added three event types, and then directly
>   implemented the leads-to relation.

With the consequence that we had to make up a new
mechanism for drawing consequences about what must
have happened to make an event possible.

The mechanism we built had a drawback:  If a state
event e appears in a skeleton, then the analysis
never terminates unless there is a fixed finite
bound to the length of all histories that could
lead to the state in e.

>   Think about what a write up of all of this
>   will look like.  Above all else, it should be
>   easy to explain.

Yes.

1.  State based reasoning uses the same form of
    the authentication tests that channels do.
    Specifically, every state location is a
    *confidential* channel.

    Moreover, if a state value is definitely
    non-initial, then a regular event must
    previously have stored it.  This means that
    state locations have the *authentic* property
    for definitely non-initial values, which we
    call gen-state values.

    Slogan:  Writing a state value is a
    confidential message into the future.  Reading
    a state value is an authentic message out of
    the past if the state value is gen-state.

2.  There are some other properties of state vs
    channels of other kind that will be
    "axiomatized" via rules.

    a.  Transition events, which take exclusive
    possession of a state location and change the
    value, should be distinguished from
    observations, merely read and do not require
    exclusion with other reads.

    Observations on a common version of a state
    value need not be comparable in the ordering.

    b.  We need a notion of immediate causality
    for transitions.  A transition e1 may be the
    event that establishes a state value in a
    location.  If an observation or another
    transition e2 obtains this state value
    directly from e1, we say that e1 *leads to*
    e2, and let's write e1 ~> e2.

    Naturally, e1 ~> e2 implies e1<e2 and that e1
    and e2 are state events on a common location.  

    c.  There are two core properties of *leads
    to*, combined with *transition* and
    *observation*.

    (i) If e1 ~> e2 are transitions and e3 is a
        transition on the same location, then:

        e1<e3 implies (e2=e3 or e2<e3)
        e3<e2 implies (e1=e3 or e3<e1)

        (Discrete ordering)

    (ii) If e1 ~> e2 are transitions and e3 is an
        observation with e1 ~> e3, then e2<e3.

    These jointly imply that that the transition
    events on any one location form a collection
    of finite discrete linear chains under ~>,
    with no two pieces having any ~> relations.

    If a transition leads to an observation, then
    that observation precedes any subsequent
    members of the chain.

    So the laws (i)--(ii) justify a clear
    state-like semantics.   

3.  We decided to represent transition events by 
    load-store pairs of events on one location.

4.  I chose to define leads-to by adding points
    (representing the space-time point of the
    transition, in a non-metric way).

    Then e1 ~> e2 just means that e1 is the store
    component of a load-store pair, and e2 is a
    reception event that receives the same channel
    msg.  Hence, when the authentication test for
    the auth channel property adds an e1 to
    explain e2, it automatically causes e1 ~> e2.

    I thought this was pretty slick, though I
    wasn't ready to 100% hide the underlying point
    data values.  If I had correctly printed out
    the leads-to relation, nobody would have had
    to know that this was the implementation
    trick!

    But other alternatives are conceivable here
    without messing up 1-3.

5.  To represent state events that synchronize
    several locations, we chose to flatten them
    into

      ... load load store store ...

    segments of nested load-store pairs.  This did
    require a way to treat these as critical
    sections.  

I think this is really the whole story, apart from
a few fine points.

What do you think?  Am I leaving out other things
that really change the picture?

        Joshua 



        

        
    


-- 
	Joshua Guttman
	The MITRE Corp.
	
