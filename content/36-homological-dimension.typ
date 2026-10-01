#import "main-defs.typ": (
  Coker, Ext, HCat, Hom, Im, Ker, Res, ann, hd, idx, maxSpec, moduleCategory,
  name-idx, rad, rtGlDim, source, spec, symbol-idx,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, proof, proposition,
)

== Гомологическая размерность модулей
<sec:homological-dimension>

Пусть $A$ — кольцо и $M in moduleCategory hyph A$. Через
$ hd_A (M) $
обозначим минимальную длину (возможно, бесконечную) проективной резольвенты
модуля $M$ (см. @ch:category-algebra, § @sec:projective-resolutions). Определим
$ rtGlDim A = sup hd_A (M) quad (M in moduleCategory hyph A). $
#symbol-idx($hd$, sort: "hd", group: "operators", order: 51)
#symbol-idx($rtGlDim$, sort: "rt gl. dim", group: "operators", order: 71)
Приведем без доказательства следующий полезный результат Ауслендера (см. книгу
Маклейна @bib:MacLane1963, гл. VII, следствие (1.5)).
#name-idx("Маклейн (MacLane S.)")
#proposition(title: [Ауслендер])[
  $ rtGlDim A = sup hd_A (M) quad (M in bold(M)(A)). $
] <prop:auslander-global-dimension>
#idx("теорема", "Ауслендера")
Из @th:semisimple-ring-characterizations следует, что $rtGlDim A = 0$ тогда и
только тогда, когда кольцо $A$ полупросто. Если $rtGlDim A <= 1$, то назовем
кольцо $A$ _наследственным справа_. #idx("наследственное справа кольцо")

#proposition[
  #condition-list[
    #condition-item(format: "cyrillic")[Кольцо $A$ наследственно справа тогда и
      только тогда, когда каждый его правый идеал
      проективен.] <cond:hereditary-projective-right-ideals>

    #condition-item(format: "cyrillic")[Пусть кольцо $A$ наследственно справа и
      нётерово справа. Пусть $M in bold(M)(A)$ и $T = inter Ker(h)$
      ($h\: M arrow.r A$). Тогда $T$ — прямое слагаемое в $M$ и $M slash T$
      является прямой суммой модулей, которые изоморфны правым идеалам кольца
      $A$.] <cond:hereditary-torsionless-decomposition>
  ]
] <prop:hereditary-ring-ideals>
#proof[
  @cond:hereditary-projective-right-ideals Если $frak(a)$ — правый идеал, то
  рассмотрение точной последовательности
  $ 0 arrow.r frak(a) arrow.r A arrow.r A slash frak(a) arrow.r 0 $
  #source(109) показывает (см. @prop:projective-dimension-sequence), что
  $[hd_A (A slash frak(a)) <= 1] <=> [hd_A (frak(a)) <= 0]$. Таким образом, все
  правые идеалы проективны тогда и только тогда, когда $hd_A (M) <= 1$ для всех
  циклических (т. е. с одним образующим) модулей $M$. Из этого следует, что
  $hd_A (M) <= 1$ для всех $M in bold(M)(A)$ и, следовательно, кольцо $A$
  наследственно справа в силу предложения @prop:auslander-global-dimension.
  Действительно, если $M$ — модуль с $n$ образующими, то рассмотрим точную
  последовательность
  $ 0 arrow.r M' arrow.r M arrow.r M'' arrow.r 0, $
  где $M'$ и $M''$ — модули с одним и с $n - 1$ образующим соответственно. В
  силу предложения @prop:projective-dimension-sequence
  $hd_A (M) <= sup(hd_A (M'), hd_A (M''))$, поэтому утверждение доказывается
  индукцией по $n$.

  @cond:hereditary-torsionless-decomposition Если мы покажем, что $M slash T$
  является прямой суммой модулей, которые изоморфны правым идеалам, то из п.
  @cond:hereditary-projective-right-ideals следует, что модуль $M slash T$
  проективен, откуда $M approx.eq T plus.o M slash T$. Так как кольцо $A$
  нётерово справа, то модуль $M slash T in bold(M)(A)$ нётеров. Среди всех
  прямых слагаемых модуля $M slash T$, являющихся прямыми суммами модулей,
  которые изоморфны правым идеалам (таков, например, нулевой подмодуль), выберем
  максимальное, пусть это подмодуль $N$. Тогда $M slash T = N plus.o H$.
  Утверждаем, что $H = 0$. Если это не так, то найдется ненулевой гомоморфизм
  $h\: H arrow.r A$. Так как $Im(h)$ — ненулевой проективный модуль, то
  $H approx.eq Ker(h) plus.o Im(h)$, и тогда рассмотрим модуль $N plus.o Im(h)$.
  Получаем противоречие с максимальностью модуля $N$.
]

Введем в рассмотрение полную подкатегорию
$ HCat(A) $
модулей $M in moduleCategory hyph A$, обладающих конечными
$bold(P)(A)$-резольвентами. Очевидно, что
$ bold(P)(A) subset HCat(A) subset bold(M)(A) subset moduleCategory hyph A, $
и если $M in HCat(A)$, то $hd_A (M) < infinity$. С другой стороны, если
$M in bold(M)(A)$ и $hd_A (M) < infinity$, то модуль $M$ может и не принадлежать
категории $HCat(A)$. Действительно, модуль $M$ должен быть не только конечно
порожденным, но, в частности, и конечно представимым. В обозначениях
(@ch:category-algebra, § @sec:projective-resolutions) $HCat(A)$ является
категорией $Res(bold(P)(A))$. Вспомним следующее утверждение из следствия
@cor:resolvable-subcategories.

#proposition[
  Если известно, что все, кроме одного, члены точной последовательности
  $ 0 arrow.r M_n arrow.r dots arrow.r M_0 arrow.r 0 $
  принадлежат $HCat(A)$, то и этот оставшийся член также лежит в $HCat(A)$.
] <prop:finite-projective-resolutions-extension>

#source(110) Кольцо $A$ называется _регулярным справа_, если
$HCat(A) = bold(M)(A)$. Из предложения
@prop:finite-projective-resolutions-extension немедленно следует, что кольцо $A$
обязано быть нётеровым справа. Обратно, если кольцо $A$ нётерово справа и если
$hd_A (M) < infinity$ для всех $M in bold(M)(A)$, то кольцо $A$ регулярно
справа. Действительно, если $hd_A (M) <= n$, то выберем точную
последовательность
$ 0 arrow.r P_n arrow.r P_(n-1) arrow.r dots arrow.r P_0 arrow.r M arrow.r 0, $
где $P_i in bold(P)(A)$ для $0 <= i < n$ и $P_n in bold(M)(A)$. Это возможно,
поскольку кольцо $A$ нётерово справа. Из леммы Шанюэля (см.
@cor:generalized-schanuel) следует автоматически, что $P_n$ — проективный
модуль, и поэтому $P_n in bold(P)(A)$.
#idx("регулярное справа кольцо")

#proposition[
  Пусть $S$ — мультипликативная система в коммутативном кольце $R$. Пусть $A$ —
  произвольная $R$-алгебра и $M$ принадлежит $moduleCategory hyph A$. Тогда
  $ hd_(S^(-1)A)(S^(-1)M) <= hd_A (M), quad rtGlDim S^(-1)A <= rtGlDim A, $
  и если кольцо $A$ регулярно справа, то кольцо $S^(-1)A$ также регулярно
  справа.
] <prop:localization-homological-dimension>
#proof[
  Если $P arrow.r M$ — проективная $A$-резольвента длины $n$, то
  $S^(-1)P arrow.r S^(-1)M$ является проективной $S^(-1)A$-резольвентой
  (поскольку функтор $S^(-1)$ точен), и ее длина $<= n$. Так как каждый
  $N in moduleCategory hyph S^(-1)A$ изоморфен некоторому модулю $S^(-1)M$, то
  второе неравенство следует из первого. Если кольцо $A$ нётерово справа, то
  кольцо $S^(-1)A$ также нётерово справа, и любой модуль $N in bold(M)(S^(-1)A)$
  изоморфен модулю $S^(-1)M$ для некоторого $M in bold(M)(A)$. Следовательно,
  последнее утверждение следует из первого неравенства, что и требовалось
  доказать.
]

#proposition[
  Пусть $A$ является $R$-алгеброй, и пусть $M in moduleCategory hyph A$.
  Определим
  $ U_n (M) = {frak(p) in spec(R) | hd_(A_(frak(p)))(M_(frak(p))) <= n}. $
  Если существует точная последовательность
  $
    P_(n+1) arrow.r P_n arrow.r dots arrow.r P_0 limits(arrow.r)^epsilon M
    arrow.r 0,
  $
  где $P_i in bold(P)(A)$ ($0 <= i <= n+1$), то множество $U_n (M)$ открыто и
  $[hd_A (M) <= n] <=> [U_n (M) = spec(R)]$.
] <prop:projective-dimension-open-locus>
#proof[
  Индукция по $n$.

  $n = 0$. Нам дана точная последовательность
  $ P_1 arrow.r P_0 limits(arrow.r)^epsilon M arrow.r 0, $
  где $P_i in bold(P)(A)$ ($i = 0,1$). Рассмотрим отображение
  $ h\: Hom_A (M,P_0) arrow.r Hom_A (M,M), $
  #source(111) индуцированное гомоморфизмом $epsilon$. Пусть $e$ обозначает
  образ элемента $1_M$ в $Coker(h)$. Очевидно, что [модуль $M$ проективен]
  $<=> [1_M in Im(h)] <=> [e = 0]$. Так как оба $A$-модуля $P_0$ и $M$ конечно
  представимы, то из предложения @prop:localization-hom-finite-presentation
  следует, что для $frak(p) in spec(R)$ можно отождествить соответствующее
  отображение
  $
    Hom_(A_(frak(p)))(M_(frak(p)),P_(0 frak(p))) arrow.r
    Hom_(A_(frak(p)))(M_(frak(p)),M_(frak(p)))
  $
  с локализацией $h_(frak(p))$ отображения $h$. Итак, [$M_(frak(p))$ есть
  $A_(frak(p))$-проективный модуль] $<=>$
  [$e_(frak(p)) = e slash 1 in Coker(h)_(frak(p)) (= Coker(h_(frak(p))))$ —
  нулевой элемент]. Но $[e_(frak(p)) = 0 <=> e s = 0$ для некоторого
  $s in.not frak(p)] <=> [frak(a) subset.not frak(p)$, где
  $frak(a) = ann_R (e)]$, и поэтому $U_0(M)$ является (открытым) дополнением к
  $V(frak(a))$. Кроме того, [модуль $M$ проективен]
  $<=> [e = 0] <=> [frak(a) = R] <=> [V(frak(a)) = emptyset] <=> [U_0(M) =
    spec(R)]$.

  $n > 0$. Рассмотрим точную последовательность
  $ 0 arrow.r K arrow.r P_0 limits(arrow.r)^epsilon M arrow.r 0, $
  где $K = Ker(epsilon)$. Тогда $[hd_A (M) <= n] <=> [hd_A (K) <= n - 1]$ и
  $U_n (M) = U_(n-1)(K)$. Так как последовательность
  $ P_(n+1) arrow.r P_n arrow.r dots arrow.r P_1 arrow.r K arrow.r 0 $
  точна и $P_i in bold(P)(A)$ ($1 <= i <= n + 1$), то из индуктивного
  предположения следует, что $U_(n-1)(K)$ — открытое множество и что
  $[hd_A (K) <= n - 1] <=> [U_(n-1)(K) = spec(R)]$, что и требовалось доказать.
]

#corollary[
  Пусть $R$ — коммутативное нётерово кольцо, $A$ — конечномерная $R$-алгебра и
  $M in bold(M)(A)$. В этом случае $hd_A (M) = sup
  hd_(A_(frak(m)))(M_(frak(m)))$ ($frak(m) in maxSpec(R)$), и если
  $hd_(A_(frak(m)))(M_(frak(m))) <
  infinity$ для всех $frak(m) in maxSpec(R)$, то $hd_A (M) < infinity$.
  Следовательно, кольцо $A$ регулярно справа тогда и только тогда, когда
  $A_(frak(m))$ — регулярное справа кольцо для всех $frak(m) in maxSpec(R)$.
] <cor:local-global-projective-dimension>
#proof[
  Ясно, что последнее утверждение следует из первого. Пусть
  $n = sup hd_(A_(frak(m)))(M_(frak(m)))$ ($frak(m) in maxSpec(R)$). В силу
  предложения @prop:localization-homological-dimension $hd_A (M) >= n$. Поэтому
  если $n = infinity$, то имеет место равенство. Если $n < infinity$, то
  рассмотрим $U_n (M)$. Наши предположения показывают, что предпосылки
  предложения @prop:projective-dimension-open-locus относительно $M$
  автоматически выполнены и потому $U_n (M)$ является открытым множеством,
  дополнение которого не содержит максимальных идеалов и, следовательно, пусто.
  (Если $V(frak(a)) inter maxSpec(R) = emptyset$, то идеал не содержится ни в
  одном максимальном идеале, поэтому $frak(a) = R$.) Итак, $U_n (M) = spec(R)$,
  и из предложения @prop:projective-dimension-open-locus теперь следует, что
  $hd_A (M) <= n$.

  #source(112) Если $hd_(A_(frak(m)))(M_(frak(m))) < infinity$ для всех
  $frak(m) in maxSpec(R)$, то в силу предложения
  @prop:localization-homological-dimension это же верно и для всех
  $frak(m) in spec(R)$. Следовательно, в этом случае объединение всех $U_n (M)$
  совпадает с $spec(R)$. Так как $U_n subset U_(n+1)$ и пространство $spec(R)$
  квазикомпактно (даже нётерово в данном случае), то $U_n (M) = spec(R)$ для
  некоторого $n$. Применим предложение @prop:projective-dimension-open-locus и
  получим, что $hd_A (M) <= n$, что и требовалось доказать.
]

Пусть $R$ — коммутативное кольцо, $A$ — произвольная $R$-алгебра и $S$ —
мультипликативная система в $R$. Назовем $M in moduleCategory hyph A$
_$S$-периодическим модулем_, если $S^(-1)M = 0$. Обозначим через
$ HCat_S (A) subset bold(M)_S (A) $
полные подкатегории $S$-периодических модулей в $HCat(A)$ и в $bold(M)(A)$
соответственно. Легко видеть, что $M in moduleCategory hyph A$ принадлежит
$bold(M)_S (A)$ тогда и только тогда, когда $M in bold(M)(A)$ и $M_s = 0$ для
некоторого $s in S$. Последнее означает, что $S inter ann_R (M) != emptyset$.
Будем говорить, что система $S$ _регулярна относительно алгебры_ $A$, если
$HCat_S (A) = bold(M)_S (A)$. Нетрудно показать с помощью предложения
@prop:finite-projective-resolutions-extension, что последняя категория в этом
случае является абелевой категорией, в которой каждый объект нётеров. #idx(
  "S-периодический модуль",
)#idx("регулярная относительно алгебры система")
#symbol-idx($HCat_S$, sort: "H_S", group: "categories", order: 12)
#symbol-idx($bold(M)_S$, sort: "M_S", group: "categories", order: 17)

#proposition[
  Пусть $R$ — коммутативное нётерово кольцо и $A$ — конечномерная $R$-алгебра.

  #condition-list[
    #condition-item(format: "cyrillic")[$rtGlDim A = sup hd_A (M)$, где $M$
      пробегает все простые правые $A$-модули. Следовательно, если кольцо $R$
      полулокально и если кольцо $A$ регулярно справа, то
      $rtGlDim A < infinity$.] <cond:finite-algebra-simple-global-dimension>

    #condition-item(format: "cyrillic")[Пусть $S$ — мультипликативная система в
      $R$. Система $S$ регулярна относительно алгебры $A$ тогда и только тогда,
      когда кольцо $A_(frak(m))$ регулярно справа для всех
      $frak(m) in maxSpec(R)$, таких, что $frak(m) inter S != emptyset$. В этом
      случае, если $M in bold(M)(A)$, то
      $
        M in HCat(A) <=> S^(-1)M in HCat(S^(-1)A).
      $] <cond:finite-algebra-local-regular-system>
  ]
] <prop:finite-algebra-global-dimension-regularity>
#proof[
  @cond:finite-algebra-simple-global-dimension Левая сторона не меньше, чем
  правая, и равна $sup hd_A (M)$ ($M in bold(M)(A)$) (в силу теоремы Ауслендера
  @prop:auslander-global-dimension). В частности, если $n = sup {hd_A (M) | M$ —
  простой модуль$}$ бесконечно, то получим равенство. Поэтому предположим, что
  $n < infinity$. Пусть дан модуль $M in bold(M)(A)$. Покажем, что
  $hd_A (M) <= n$. В силу @cor:local-global-projective-dimension достаточно
  показать это локально. Поэтому предположим, что $R$ — локальное кольцо с
  максимальным идеалом $frak(m)$.

  Пусть $frak(a)$ — идеал в $R$. Покажем, что если $M in bold(M)(A)$ и
  $M frak(a) = 0$, то $hd_A (M) <= n$ (из этого утверждения при $frak(a) = 0$
  получается искомый результат). Если это не так, то пусть $frak(a)$ —
  максимальный «плохой» идеал (используется нётеровость). Выберем
  $M in bold(M)(A)$, такой, что $M frak(a) = 0$ и $hd_A (M) > n$. Тогда выберем
  максимальный подмодуль $N subset M$, такой, что $hd_A (M slash N) > n$.
  Заменяя $M$ #source(113) на $M slash N$, можно считать, что $hd_A (M') <= n$
  для всех собственных фактормодулей модуля $M$. Равенство $frak(a) = frak(m)$
  невозможно, так как тогда длина модуля $M$ была бы конечной и гомологическая
  размерность его факторов ряда Жордана — Гёльдера ограничивала бы
  гомологическую размерность модуля $M$ (см. предложение
  @prop:projective-dimension-sequence). Таким образом, можно выбрать
  $t in frak(m)$, $t in.not frak(a)$. Если $N = Ker(M limits(arrow.r)^t M)$, то
  $ann_R (N) supset frak(a) + t R$, и поэтому $hd_A (N) <= n$. Если $N != 0$, то
  также $hd_A (M slash N) <= n$, и, следовательно, $hd_A (M) <= n$, что
  противоречит предположению (опять использовали предложение
  @prop:projective-dimension-sequence). Следовательно, имеет место точная
  последовательность
  $
    0 arrow.r M limits(arrow.r)^t M arrow.r M slash (M t) arrow.r 0.
  $ <eq:homological-dimension-multiplication-sequence>
  В этом месте применим функтор $Ext$ и используем его свойства, с которыми
  читатель может познакомиться, например, по книге Картана и Эйленберга
  @bib:Cartan1956. Последовательность
  @eq:homological-dimension-multiplication-sequence индуцирует точную
  последовательность
  $
    Ext_A^n (M,H) limits(arrow.r)^t Ext_A^n (M,H) arrow.r Ext_A^(n+1)(M
      slash (M t),H)
  $
  для всех $H in moduleCategory hyph A$. Так как $hd_A (M) > n$, то известно,
  что можно найти $H in bold(M)(A)$, для которого $Ext_A^n (M,H) != 0$. Но
  последний является конечно порожденным $R$-модулем, и
  $Ext_A^(n+1)(M slash (M t),H) = 0$. Так как $t in rad R$, то это противоречит
  лемме Накаямы, что и требовалось доказать. #name-idx(
    "Картан (Cartan H.)",
  )#name-idx("Эйленберг (Eilenberg S.)")
  #symbol-idx($Ext$, sort: "Ext", group: "operators", order: 47)

  @cond:finite-algebra-local-regular-system Допустим, что система $S$ регулярна
  относительно алгебры $A$ и что $frak(m) in maxSpec(R)$, при этом
  $frak(m) inter S != emptyset$. Если $M$ — простой $A_(frak(m))$-модуль, то $M$
  — простой $A slash (frak(m)A)$-модуль, и поэтому $hd_A (M) < infinity$. В силу
  следствия @cor:local-global-projective-dimension,
  $hd_(A_(frak(m)))(M) <= hd_A (M)$. Поэтому из п.
  @cond:finite-algebra-simple-global-dimension вытекает, что
  $rtGlDim A_(frak(m)) < infinity$. В частности, кольцо $A_(frak(m))$ регулярно
  справа.

  Обратно, предположим, что кольцо $A_(frak(m))$ регулярно справа для любого
  $frak(m)$, такого, что $frak(m) inter S != emptyset$. Пусть $M in bold(M)(A)$,
  и предположим, что $hd_(S^(-1)A)(S^(-1)M) < infinity$. Покажем, что тогда
  $hd_A (M) < infinity$. (Импликация в противоположном направлении вытекает из
  следствия @cor:local-global-projective-dimension.) Кроме того, из этого
  утверждения (в частном случае $S^(-1)M = 0$) следует, что система $S$
  регулярна относительно алгебры $A$.

  В силу следствия @cor:local-global-projective-dimension достаточно показать,
  что $hd_(A_(frak(m)))(M_(frak(m))) < infinity$ для всех $frak(m) in
  maxSpec(R)$. Если $frak(m) inter S = emptyset$, то кольцо $A_(frak(m))$
  является локализацией кольца $S^(-1)A$ и $hd_(S^(-1)A)(S^(-1)M) < infinity$.
  Если $frak(m) inter S != emptyset$, то по предположению кольцо $A_(frak(m))$
  регулярно справа, поэтому $hd_(A_(frak(m)))(M_(frak(m))) < infinity$, что и
  требовалось доказать.
]
