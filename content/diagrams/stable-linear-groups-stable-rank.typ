#import "../main-defs.typ": SR
#import "commutative.typ": cd, edge

#let diagram-stable-rank() = [
  $
    #cd(
      cell-size: (34mm, 22mm),
      $SR'_n (A, frak(q)) & SR''_n (A, frak(q)) & SR_m (A, frak(q)) "(для" m >= n ")" \ & SR_n (A, frak(q)) & \ SR_n (A, frak(q)_0) & & SR_n (A slash frak(q)_0, frak(q) slash frak(q)_0)$,
      edge(
        (1, 1),
        "ul",
        $#[@th:stable-rank-relative-elementary-stability]
        #[@cond:stable-rank-elementary-transitivity]$,
        "=>",
        label-side: left,
      ),
      edge(
        (1, 1),
        "u",
        $#[@th:stable-rank-relative-elementary-stability]
        #[@cond:stable-rank-linked-matrix-equivalence]$,
        "=>",
        label-side: right,
      ),
      edge((1, 1), "ur", "=>"),
      edge(
        (1, 1),
        "dl",
        $#[@prop:stable-rank-ideals-quotients]
        #[@cond:stable-rank-ideal-restriction]$,
        "=>",
        label-side: right,
      ),
      edge(
        (1, 1),
        "dr",
        $#[@prop:stable-rank-ideals-quotients]
        #[@cond:stable-rank-quotient]$,
        "=>",
        label-side: left,
      ),
    )
  $
]
