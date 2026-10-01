#import "main-defs.typ": (
  Aut, E, GE, GL, Hom, Im, Int, Ker, MC, Pic, PicCat, ann, dim, idx, maxSpec,
  moduleCategory, name-idx, rad, source, spec, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, example, proof, theorem,
)
#import "diagrams/stable-projective-diagrams.typ": map-arrow

== Теорема Сешадри <sec:seshadris-theorem>

Теорема#idx("теорема Сешадри") утверждает _при соответствующих предположениях_
следующее. Пусть $R$ — коммутативное кольцо, $S$ — мультипликативная система
кольца $R$, $A$ — $R$-алгебра и $P in bold(P)(A)$. Тогда если $S^(-1) P$ —
свободный $S^(-1) A$-модуль, то $P$ — свободный $A$-модуль. В первоначальном
варианте этой теоремы, принадлежащем Сешадри, предполагалось, что $R$ — область
главных идеалов, $S = R without {0}$ и $A = R[t]$ (кольцо многочленов от одной
переменной). В этом случае модуль $S^(-1) P$, очевидно, автоматически свободен,
и поэтому Сешадри получил, что все модули $P in bold(P)(R[t])$ свободны. Как
было замечено многими математиками, рассуждения Сешадри применимы и в более
общем случае. Мы приведем здесь эти обобщения. Хотя необходимые предположения
весьма ограничительны, тем не менее им удовлетворяют некоторые некоммутативные
$R$-алгебры $A$. Кроме того, в дальнейшем будет полезно рассматривать более
общие мультипликативные системы, чем встречавшиеся до сих пор; с этого мы и
начнем.

Пусть $R$ — коммутативное кольцо, $S$ — мультипликативная система обратимых
идеалов кольца $R$. Мы собираемся построить функтор локализации
$M arrow.r.bar S^(-1) M$ на категории $moduleCategory hyph R$ в категорию
$moduleCategory hyph S^(-1) R$, обладающий всеми свойствами обычной локализации,
#source(175)с которой он совпадает в том случае, когда все идеалы в системе $S$
главные. Пусть $L$ — полное кольцо частных кольца $R$. Тогда если
$frak(a) in S$, то $frak(a)^(-1) subset L$ и
$
  S^(-1) R = union frak(a)^(-1) quad (frak(a) in S)
$
является, очевидно, подкольцом кольца $L$. Более удобная запись:
$
  S^(-1) R = limits(lim)_(arrow.r) frak(a)^(-1) quad (frak(a) in S);
$
при этом отображения в индуктивной системе являются вложениями. Если
$M in moduleCategory hyph R$, то положим
$
  S^(-1) M & = limits(lim)_(arrow.r) (M tensor_R frak(a)^(-1)) \
           & = M tensor_R (limits(lim)_(arrow.r) frak(a)^(-1)) \
           & = M tensor_R S^(-1) R.
$
Воспользуемся теперь тем, что функторы $tensor_R$ и $limits(lim)_(arrow.r)$
перестановочны. Так как функтор $tensor_R frak(a)^(-1)$ точен (идеал
$frak(a)^(-1)$ проективен) и так как функтор $limits(lim)_(arrow.r)$ также
точен, то $S^(-1)$ — точный функтор из $moduleCategory hyph R$ в
$moduleCategory hyph S^(-1) R$.

Имеет место естественный гомоморфизм
$
  M = M tensor_R R -> S^(-1) M;
$
его ядро совпадает (см. @prop:direct-limit-elements) с объединением модулей
$Ker(M tensor_R R -> M tensor_R frak(a)^(-1))$ ($frak(a) in S$). Покажем, что
последнее в точности равно $ann_M (frak(a)) = {x in M | x frak(a) = 0}$. Так как
идеал $frak(a)$ конечно порожден (ибо обратим), то достаточно проверить это
утверждение локально. Следовательно, можно считать, что идеал $frak(a) = a R$ —
главный. Но тогда гомоморфизмы $M tensor_R R -> M tensor_R a^(-1) R$ и
$M #map-arrow($a$) M$ изоморфны, а ядро последнего совпадает с $ann_M (a)$.

Пусть $A$ — $R$-алгебра. Тогда очевидно, что $S^(-1) A$ является
$S^(-1) R$-алгеброй и $S^(-1)$ индуцирует точный функтор
$
  S^(-1): moduleCategory hyph A -> moduleCategory hyph S^(-1) A.
$
Покажем, что если $M in MC(A)$, то
$
  [S^(-1) M = 0] <=> [M frak(a) = 0 quad
    "для некоторого идеала" frak(a) in S].
$
Импликация $<=$ очевидна. Для доказательства обратной импликации применим
сказанное непосредственно выше к каждой конечной системе $A$-образующих модуля
$M$. Пусть $frak(a)$ — произведение полученных аннуляторных идеалов.

Мы получаем естественный гомоморфизм $S^(-1) R$-модулей
$
  h_P: S^(-1) Hom_A (P, M) -> Hom_(S^(-1) A) (S^(-1) P, S^(-1) M)
$
#source(176)для $P, M in moduleCategory hyph A$. Очевидно, что $h_A$ —
изоморфизм, поэтому по аддитивности $h_P$ — изоморфизм для всех
$P in bold(P)(A)$. С учетом полуточности функтора и 5-леммы стандартные
рассуждения показывают, что $h_P$ — изоморфизм для любого конечно представимого
$A$-модуля $P$.

#theorem(title: [Сешадри, …])[
  Пусть $R$ — коммутативное кольцо и $S$ — мультипликативная полугруппа,
  порожденная множеством $S_0$ обратимых простых идеалов кольца $R$. Пусть $A$ —
  $R$-алгебра, являющаяся точным и плоским $R$-модулем и такая, что
  $A/(A frak(p))$ — обобщенное $n$-евклидово кольцо (см.
  @def:generalized-euclidean-ring) и
  $(A frak(a))/(A frak(a) frak(p)) tilde.eq A/(A frak(p))$ для любых
  $frak(p) in S_0$ и $frak(a) in S$. Пусть модули
  $P, L_1, dots, L_n in bold(P)(A)$ таковы, что
  $L_i/(L_i frak(p)) tilde.eq A/(A frak(p))$ ($1 <= i <= n$) для всех
  $frak(p) in S_0$ и $S^(-1) P tilde.eq S^(-1) L$, где
  $L = L_1 plus.o dots plus.o L_n$. Тогда найдется такой элемент $frak(a)$
  группы $overline(S)$, порожденной полугруппой $S$, что
  $
    P tilde.eq L_1 frak(a) plus.o L_2 plus.o dots plus.o L_n.
  $ <eq:seshadri-projective-splitting>
  #idx("теорема Сешадри")
  Кроме того, если элементы $frak(a)_1, dots, frak(a)_n in overline(S)$ таковы,
  что $frak(a)_1 dots frak(a)_n tilde.eq R$, то
  $
    L tilde.eq L_1 frak(a)_1 plus.o L_2 frak(a)_2
    plus.o dots plus.o L_n frak(a)_n.
  $ <eq:seshadri-twist-redistribution>
] <th:seshadri-projective-splitting>

#corollary[
  Предположим, что в теореме @th:seshadri-projective-splitting кольцо
  $A/(A frak(p))$ является обобщенным евклидовым для всех $frak(p) in S_0$ и что
  каждый модуль из $bold(P)(S^(-1) A)$ является $S^(-1) A$-свободным. Тогда если
  $P != 0$ и $P in bold(P)(A)$, то $P tilde.eq A frak(a) plus.o A^(n - 1)$ для
  некоторых $frak(a) in overline(S)$ и $n > 0$.
] <cor:localized-free-projective-ideal-splitting>

#proof(head: [Доказательство следствия.])[
  По предположению $S^(-1) P tilde.eq S^(-1)(A^n)$ для некоторого $n > 0$, и
  поэтому в теореме можно взять $L_i = A$ для любого $i$.
]

#example(plural: true)[
  Предположим, что $A$ и $B$ являются пополненными $R$-алгебрами, для которых
  справедливы предположения теоремы @th:seshadri-projective-splitting по
  отношению к $S_0$ и $S$. Тогда они выполнены и в алгебре $A ast_R B$ (это
  следует из @th:cohn-free-product-firs).

  Пусть $R$ — дедекиндово кольцо и $A = R pi$, где $pi$ — свободная группа или
  полугруппа. Тогда из @cor:free-monoid-algebra-generalized-euclidean следует,
  что кольцо $A/(A frak(p))$ является обобщенным евклидовым для всех
  $frak(p) in maxSpec(R)$. Это же верно и для алгебры $S^(-1) A$, где $S^(-1) R$
  — поле частных кольца $R$. Таким образом, применимо следствие
  @cor:localized-free-projective-ideal-splitting.
] <exm:seshadri-free-products-and-monoids>

#corollary[
  Пусть $R$ — дедекиндово кольцо и $pi$ — свободная группа или полугруппа. Если
  $P in bold(P)(R pi)$, $P != 0$, то
  $P tilde.eq (R pi tensor_R L) plus.o (R pi)^(n - 1)$ для некоторого
  $L in PicCat(R)$ и некоторого $n > 0$.
] <cor:projective-modules-free-monoid-pid>

#proof(head: [Доказательство теоремы @th:seshadri-projective-splitting.])[
  Проведем доказательство в несколько шагов.

  #source(177)
  #condition-list[
    #condition-item(format: "degree")[_Если $H in bold(P)(A)$,
      $frak(a) in overline(S)$ и $frak(p) in S_0$, то
      $H frak(a) tilde.eq H tensor_R frak(a)$ и
      $(H frak(a))/(H frak(a) frak(p)) tilde.eq H/(H frak(p))$._
      (Мы считаем, что
      $H frak(a) subset S^(-1) H$.)] <cond:seshadri-twist-reduction>

    Так как $A$ является $R$-плоским модулем, то таков же и модуль $H$
    ($in bold(P)(A)$). Следовательно, функтор $H tensor_R$ сохраняет точность
    последовательности $0 -> frak(a) -> S^(-1) R$, и поэтому можно отождествить
    $H tensor_R frak(a)$ с $H frak(a) subset H tensor_R S^(-1) R = S^(-1) H$. Мы
    видим, что в случае $frak(a) = R$ модуль $H$ вкладывается в $S^(-1) H$.

    Предположим, что $frak(a) in S$. Тогда
    $
      (H frak(a))/(H frak(a) frak(p))
      & tilde.eq H tensor_R (frak(a)/(frak(a) frak(p))) \
      & tilde.eq (H tensor_A A) tensor_R (frak(a)/(frak(a) frak(p))) \
      & tilde.eq H tensor_A ((A frak(a))/(A frak(a) frak(p))) \
      & tilde.eq H tensor_A (A/(A frak(p))) quad "(по предположению)" \
      & tilde.eq H/(H frak(p)).
    $
    В общем случае можно записать $frak(a) = frak(b) frak(c)^(-1)$, где
    $frak(b), frak(c) in S$. Тогда
    $
      (H frak(a))/(H frak(a) frak(p))
      tilde.eq (H frak(c)^(-1))/(H frak(c)^(-1) frak(p))
      tilde.eq H/(H frak(p))
    $
    (мы применяем рассмотренный выше частный случай к $H frak(c)^(-1)$ и
    $frak(b)$ и к $H frak(c)^(-1)$ и $frak(c)$ соответственно). Этим доказано
    утверждение @cond:seshadri-twist-reduction.

    Под _расщеплением_ модуля $H in bold(P)(A)$#idx("расщепление модуля") мы
    будем понимать разложение в прямую сумму $H = H_1 plus.o dots plus.o H_n$,
    такое, что $H_i/(H_i frak(p)) tilde.eq A/(A frak(p))$ для всех
    $frak(p) in S_0$ ($1 <= i <= n$).

    #condition-item(format: "degree")[_Пусть $H = H_1 plus.o dots plus.o H_n$ —
    расщепляющийся подмодуль модуля $Q in bold(P)(A)$. Допустим, что
    $Q frak(b) frak(p) subset H$ для некоторых $frak(p) in S_0$ и
    $frak(b) in S$. Тогда $(H inter Q frak(p))/(H frak(p))
    tilde.eq (A/(A frak(p)))^r$ для некоторого $r$ ($0 <= r <= n$) и существует
    модуль $overline(H)$, такой, что $Q frak(b) subset overline(H) subset Q$, с
    расщеплением
    $overline(H) tilde.eq H_1 frak(p)^(-r) plus.o H_2 plus.o dots plus.o H_n$._]
    <cond:seshadri-prime-saturation>

    Рассмотрим точную последовательность $(A/(A frak(p)))$-модулей
    $
      0 -> (H inter Q frak(p))/(H frak(p)) -> H/(H frak(p))
      #map-arrow($j$) Q/(Q frak(p)).
    $
    Но $Q/(Q frak(p)) in bold(P)(A/(A frak(p)))$ и
    $H/(H frak(p)) tilde.eq (A/(A frak(p)))^n$. Таким образом, $Im(j)$ является
    подмодулем (с числом образующих $<= n$) проективного
    $(A/(A frak(p)))$-модуля. Поэтому из @prop:n-fir-free-module-images следует,
    что $Im(j)$ является $(A/(A frak(p)))$-свободным модулем. В частности,
    $H/(H frak(p)) tilde.eq Im(j) plus.o Ker(j)$ и, значит, модуль $Ker(j)$
    порождается $<= n$ образующими, а потому также является свободным модулем;
    скажем, $Ker(j) tilde.eq (A/(A frak(p)))^r$ и
    $Im(j) tilde.eq (A/(A frak(p)))^s$. Тогда из @def:n-fir
    @cond:fir-invariant-basis-number следует, что $r + s = n$. Запишем
    $M' = M/(M frak(p))$, где $M in moduleCategory hyph A$. Найдется автоморфизм
    $alpha' in Aut_(A') (H')$, такой, что
    $alpha'(H'_1 plus.o dots plus.o H'_r) = Ker(j)$, и, следовательно,
    отображение $j$ инъективно на $alpha'(H'_(r + 1) plus.o dots plus.o H'_n)$.
    Но $Aut_(A') (H') tilde.eq GL_n (A') = GE_n (A')$ (последнее равенство
    справедливо, поскольку кольцо $A'$ — обобщенное $n$-евклидово). Значит,
    можно записать $alpha' = epsilon' delta'$, где
    $epsilon' in E(H'_1, dots, H'_n)$ и преобразование $delta'$ задается
    диагональной матрицей относительно базиса, состоящего из элементов различных
    $H'_i$. Так как $delta'(H'_i) = H'_i$ для каждого $i$, то также
    $Ker(j) = epsilon'(H'_1 plus.o dots plus.o H'_r)$. В силу
    @prop:elementary-group-quotient-surjection существует элемент
    $epsilon in E(H_1, dots, H_n)$, равный $epsilon'$ по модулю $frak(p)$.

    #source(178)Пусть $G = epsilon(H_1 plus.o dots plus.o H_r)$, так что
    $G + H frak(p) = H inter Q frak(p)$. Положим
    $
      overline(H) & = G frak(p)^(-1)
                    plus.o epsilon(H_(r + 1) plus.o dots plus.o H_n) \
                  & = G frak(p)^(-1) + H = (H inter Q frak(p)) frak(p)^(-1).
    $
    Так как $Q frak(b) frak(p) subset H inter Q frak(p)$, то
    $Q frak(b) subset (H inter Q frak(p)) frak(p)^(-1) = overline(H)$. Осталось
    лишь показать, что
    $
      overline(H) tilde.eq H_1 frak(p)^(-r) plus.o H_2 plus.o dots plus.o H_n.
    $ <eq:seshadri-saturation-splitting>
    Мы знаем, что $overline(H) frak(p) subset H$ и
    $(overline(H) frak(p))/(H frak(p)) tilde.eq (A/(A frak(p)))^r$ для
    некоторого $r$ ($0 <= r <= n$). В этих условиях докажем справедливость
    соотношения @eq:seshadri-saturation-splitting, проведя индукцию по $r$. Если
    $r = 0$, то $overline(H) frak(p) = H frak(p)$, и поэтому $overline(H) = H$.
    Допустим теперь, что $r > 0$. Выберем, как и раньше, элемент $epsilon$ и
    положим
    $K = epsilon(H_1) frak(p)^(-1) plus.o epsilon(H_2 plus.o dots plus.o H_n)$.
    Используя утверждение @cond:seshadri-twist-reduction, убеждаемся, что мы
    получили расщепление модуля $K subset overline(H)$. Очевидно, что
    $(overline(H) frak(p))/(K frak(p))
    tilde.eq (A/(A frak(p)))^(r - 1)$. Следовательно, по предположению индукции
    $overline(H) tilde.eq epsilon(H_1) frak(p)^(-r)
    plus.o epsilon(H_2 plus.o dots plus.o H_n)
    tilde.eq H_1 frak(p)^(-r) plus.o H_2 plus.o dots plus.o H_n$.

    #condition-item(format: "degree")[_Имеет место изоморфизм
    #[@eq:seshadri-twist-redistribution]._] <cond:seshadri-redistribute-twists>

    Так как $overline(S)$ — свободная абелева группа с базисом $S_0$, то
    достаточно показать, что если $frak(p) in S_0$ и $i != j$, то
    $L tilde.eq L_i frak(p)^(-1) plus.o L_j frak(p)
    plus.o plus.o.big_(k != i, j) L_k$. Действительно, в силу
    @cond:seshadri-twist-reduction правая часть является новым расщеплением
    модуля $L$, и изоморфизм @eq:seshadri-twist-redistribution может быть
    поэтому реализован как композиция конечной последовательности изоморфизмов
    рассмотренного типа.

    Для доказательства указанного изоморфизма можно считать, не теряя общности и
    выигрывая в простоте записи, что $(i, j) = (1, 2)$. Пусть
    $H = L_1 plus.o L_2 frak(p) plus.o L_3 plus.o dots plus.o L_n
    subset L$. Тогда $L frak(p) subset H$ и
    $(L frak(p))/(H frak(p)) tilde.eq (L_2 frak(p))/(L_2 frak(p)^2)
    tilde.eq L_2/(L_2 frak(p)) tilde.eq A/(A frak(p))$ (мы используем
    @cond:seshadri-twist-reduction). В силу @cond:seshadri-prime-saturation
    можно заключить, что $L tilde.eq L_1 frak(p)^(-1)
    plus.o L_2 frak(p) plus.o L_3 plus.o dots plus.o L_n$.

    #condition-item(format: "degree")[_Имеет место изоморфизм
    #[@eq:seshadri-projective-splitting]._] <cond:seshadri-main-splitting>

    В силу наших предположений можно отождествить $S^(-1) P$ с $S^(-1) L$.
    Каждый элемент из $(S^(-1) P)/P$ аннулируется некоторым элементом из $S$.
    Если мы применим это замечание к образам в $(S^(-1) P)/P$ конечной системы
    образующих модуля $L$, то получим элемент $frak(a) in S$, такой, что
    $L frak(a) subset P$. Положим
    $H = L frak(a) = L_1 frak(a) plus.o dots plus.o L_n frak(a)$. Можно также
    найти элемент $frak(c) in S$, такой, что $P frak(c) subset H$. Из
    утверждения @cond:seshadri-redistribute-twists следует, что
    $H = H_1 plus.o H_2 plus.o dots plus.o H_n$, где $H_i tilde.eq L_i$
    ($1 < i <= n$) и ($H_1 tilde.eq L_1 frak(a)^n$). Таким образом, достаточно
    показать, что $P tilde.eq H_1 frak(a)' plus.o H_2 plus.o dots plus.o H_n$
    для некоторого $frak(a)' in overline(S)$. Для этого проведем индукцию по
    числу простых множителей (из $S_0$) элемента $frak(c)$. Если $frak(c) = R$,
    то $H = P$, и доказывать ничего не надо. В противном случае можно записать
    $frak(c) = frak(p) frak(b)$, где $frak(p) in S_0$ #source(179)и
    $frak(b) in S$. Применим @cond:seshadri-prime-saturation и найдем такой
    модуль
    $overline(H) tilde.eq H_1 frak(p)^(-r) plus.o H_2 plus.o dots plus.o H_n$
    (для некоторого $r$), что $P frak(b) subset overline(H) subset P$. Так как
    простых множителей у элемента $frak(b)$ меньше, чем у $frak(c)$, то наше
    утверждение получается теперь по индукции.
  ]

  Этим завершено доказательство теоремы @th:seshadri-projective-splitting.
]

В заключение этого параграфа дадим наброски доказательств некоторых других
следствий из теоремы Сешадри.

#corollary[
  Пусть $R$ — коммутативное нётерово кольцо размерности $<= 1$, обладающее лишь
  конечным числом необратимых максимальных идеалов. Пусть $A = R[T]$, где $T$ —
  свободная полугруппа или группа с одним образующим $t$. Тогда если ранг модуля
  $P in bold(P)(A)$ постоянен и отличен от нуля, то модуль $P$ является прямой
  суммой обратимого модуля и свободного модуля.
] <cor:one-dimensional-ring-laurent-projectives>

#proof[
  Если все максимальные идеалы кольца $R$ обратимы, то, рассматривая отдельно
  связные компоненты $spec(R)$, получаем дедекиндовы кольца и применяем
  следствие @cor:projective-modules-free-monoid-pid. Поэтому можно считать, что
  существуют необратимые максимальные идеалы. Пусть $frak(a)$ — их произведение.
  Положим $S' = 1 + frak(a)$. Если $frak(p) in maxSpec(R)$ и
  $s in frak(p) inter S'$, то идеал $frak(p)$ обратим и, значит, $R_frak(p)$ —
  кольцо дискретного нормирования. Допуская, что $spec(R)$ — связное
  пространство (это не столь существенное ограничение для нашей задачи), можно
  показать, что элемент $s$ не является делителем нуля. Это следует из того, что
  кольцо $R_frak(p)$ — область целостности, если $s in frak(p)$.

  Пусть $S_0$ — множество простых идеалов кольца $R$, порожденных максимальными
  идеалами кольца $R$, пересекающимися с $S'$. Тогда, очевидно, система $S_0$
  удовлетворяет условиям теоремы @th:seshadri-projective-splitting и кольцо
  $S^(-1) A$ из этой теоремы совпадает с $S'^(-1) A$. Если идеал
  $frak(m) in maxSpec(A)$ пересекается с $S'$, то кольцо $A_frak(m)$ является
  локализацией кольца $R_frak(p) [T]$, где $frak(p) = frak(m) inter R$. Так как
  $R_frak(p)$ — кольцо дискретного нормирования, то $R_frak(p) [T]$ — область с
  однозначным разложением, и поэтому система $S'$ факториальна относительно $A$.
  Следовательно, согласно @prop:factorial-localization-picard-surjection,
  отображение $Pic(A) -> Pic(S'^(-1) A)$ сюръективно.

  Таким образом, в силу теоремы @th:seshadri-projective-splitting следствие
  будет доказано, как только мы покажем, что утверждение следствия справедливо
  для $S^(-1) A$ вместо $A$. В свою очередь последнее утверждение будет вытекать
  из теоремы Серра (см. @cor:serre-free-summand-with-congruences и
  @cor:serre-free-summand), если мы покажем, что пространство
  $maxSpec(S^(-1) A)$ является объединением конечного числа непересекающихся
  подпространств размерности $<= 1$.

  Но $S'^(-1) A = R'[T]$, где $R' = S'^(-1) R$ — полулокальное кольцо
  размерности $<= 1$. Если $dim R' = 0$, то $dim maxSpec(R'[T]) = 1$. С другой
  стороны, если $dim R' = 1$, то $dim(R'/(rad R')) < dim(R')$, и поэтому из
  @prop:group-ring-maximal-dimension-bound следует, что пространство
  $maxSpec(R'[T])$ является объединением двух подпространств размерности $<= 1$,
  что и требовалось доказать.
]

#source(180)
#corollary[
  Пусть $pi$ — абелева группа ранга один и $A = Int pi$. Тогда утверждение
  следствия @cor:one-dimensional-ring-laurent-projectives справедливо для кольца
  $A$.
] <cor:rank-one-abelian-group-ring-projectives>

#proof[
  Переход к прямому пределу позволяет свести задачу к тому случаю, когда группа
  $pi$ конечно порождена. Тогда $pi = pi_0 times T$, где группа $pi_0$ конечна и
  $T$ — бесконечная циклическая группа. Полагая $R = Int pi_0$, мы видим, что
  $A = R[T]$ и предположения следствия
  @cor:one-dimensional-ring-laurent-projectives выполнены для $R = Int pi_0$.
  (Каждый максимальный идеал кольца $R$, не содержащий «кондуктор» (см.
  гл.~@ch:finite-group-induction, §~@sec:abelian-group-ring-conductor) из
  $Int pi_0$ в его целочисленное замыкание в кольце $bb(Q) pi_0$, обратим.)
]

С помощью усовершенствования рассмотренных методов, принадлежащего
Эндо#name-idx("Эндо (Endo S.)") @bib:Endo1963, можно доказать аналог следствия
@cor:one-dimensional-ring-laurent-projectives для случая свободной абелевой
группы или полугруппы с двумя образующими. В этом случае, однако, надо
предполагать, что $R$ — полулокальное кольцо размерности $<= 1$. Идея
доказательства заключается в том, чтобы показать, что кольцо $A = R[T]$ обладает
«большим» множеством $S_0$ обратимых простых идеалов типа рассмотренных в
@th:seshadri-projective-splitting и затем, как и ранее, что пространство
$maxSpec(S^(-1) A)$ является объединением подпространств размерности $<= 1$.
Широкое обобщение теоремы Сешадри недавно было получено Мурты#name-idx(
  "Мурты (Murthy M. P.)",
) @bib:Murthy1969. Он распространил теорему на случай координатного кольца любой
аффинной поверхности (над алгебраически замкнутым полем), бирационально
эквивалентной линейчатой поверхности.
