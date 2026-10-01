#import "main-defs.typ": (
  Aut, Coker, End, Ex, GL, H, Int, K, Ker, MC, idx, ob, source, symbol-idx,
)
#import "statements.typ": (
  condition-item, condition-list, lemma, proof, proposition, theorem,
)
#import "diagrams/abelian-k-theory-resolutions.typ": (
  projective-inverse-lifts, projective-isomorphism-lift,
  relative-resolution-functors, relative-resolution-lift, resolution-fiber,
  resolution-induction, resolution-kernel-step, resolution-lift-square,
)

== Редукция по резольвенте <sec:resolution-reduction>

Пусть $bold(C)_0 subset bold(C)$ — допустимые подкатегории абелевой категории
$bold(A)$. Цель этого параграфа — показать, что если объекты категории $bold(C)$
обладают «хорошими» резольвентами из объектов подкатегории $bold(C)_0$, то
отображения $K_i (bold(C)_0) -> K_i (bold(C))$ ($i=0,1$) являются изоморфизмами.

Пусть $0 -> A_n -> dots -> A_1 arrow.r^d A_0 -> 0$ — точная последовательность в
категории $bold(A)$, при этом $A_i in bold(C)$ для $0 <= i < n$. Тогда также
$A_n in bold(C)$. Для $n=1$ это очевидно. Для $n=2$ — это условие
@cond:admissible-kernel-closure из определения допустимой подкатегории. Общий
случай получается по индукции, примененной к последовательности
$0 -> A_n -> dots -> A_2 -> Ker d -> 0$.

Если $C=(C_n)_(n in Int)$ является конечным градуированным объектом (т. е.
$C_n=0$ почти для всех $n$) в категории $bold(C)$, то определим
$ chi(C)=chi^bold(C)(C)=sum_n (-1)^n [C_n] in K_0 (bold(C)). $
#symbol-idx($chi(C)$, sort: "χ(C)", group: "symbols", order: 134)

#source(320)
#proposition(title: [«характеристики Эйлера»])[
  #idx("характеристики Эйлера")
  #condition-list[
    #condition-item(format: "cyrillic")[Если $0 -> C' -> C -> C'' -> 0$ — точная
      последовательность конечных градуированных объектов категории $bold(C)$,
      то $chi(C)=chi(C')+chi(C'')$.] <cond:euler-graded-additivity>

    #condition-item(format: "cyrillic")[Если $C$ — конечный комплекс в категории
      $bold(C)$, для которого комплекс $H(C)$ также принадлежит $bold(C)$, то
      $chi(C)=chi(H(C))$.] <cond:euler-homology-invariance>

    #condition-item(format: "cyrillic")[Если $0 -> C' -> C -> C'' -> 0$ — точная
      последовательность комплексов, комплексы гомологии каждого из которых
      конечны и лежат в $bold(C)$, то
      $chi(H(C))=chi(H(C'))+chi(H(C''))$.] <cond:euler-exact-complex-homology>

    #condition-item(format: "cyrillic")[Пусть $f:C' -> C$ — морфизм конечных
      комплексов в категории $bold(C)$, конус отображения которого есть $MC(f)$.
      Тогда $MC(f)$ является конечным комплексом в категории $bold(C)$ и
      $chi(MC(f))=chi(C)-chi(C')$. Если $H(f)$ — изоморфизм, то
      $chi(C')=chi(C)$.] <cond:euler-mapping-cone>
  ]
] <prop:euler-characteristic-identities>

#proof[
  Утверждение @cond:euler-graded-additivity тривиально.

  @cond:euler-homology-invariance Рассмотрим точные последовательности:
  $ 0 -> Z_n -> C_n -> B_(n-1) -> 0, quad 0 -> B_n -> Z_n -> H_n -> 0. $
  Предположим, что $B_(n-1) in bold(C)$. Тогда и $Z_n in bold(C)$ (в силу первой
  последовательности). Мы допустили, что $H_n in bold(C)$, и поэтому из
  рассмотрения второй последовательности следует, что $B_n in bold(C)$. Можно
  продолжить это рассуждение. Так как $B_(n-1)=0$ для всех достаточно малых $n$,
  то можно, начиная с такого $n$ и используя приведенные соображения, показать,
  что $B_n,C_n,Z_n,H_n in bold(C)$ для всех $n$. Применяя
  @cond:euler-graded-additivity к указанным точным последовательностям, получим,
  что $chi(C)=chi(Z)-chi(B)$ и $chi(Z)=chi(H)+chi(B)$. Следовательно,
  $chi(C)=chi(H)$, что доказывает @cond:euler-homology-invariance.

  @cond:euler-exact-complex-homology Через $L$ обозначим длинную гомологическую
  последовательность последовательности $0 -> C' -> C -> C'' -> 0$,
  градуированную так, что $L_0=H_0 (C'')$. Тогда $L$ является конечным
  ацикличным комплексом в категории $bold(C)$, и поэтому из
  @cond:euler-homology-invariance следует, что $chi(L)=chi(H(L))=0$. Так как
  $chi(L)=chi(H(C''))-chi(H(C))+chi(H(C'))$, то это доказывает
  @cond:euler-exact-complex-homology.

  @cond:euler-mapping-cone Поскольку $MC(f)_(n+1)=C_(n+1) plus.o C'_n$, то
  $MC(f)$ является конечным комплексом в $bold(C)$ и
  $chi(MC(f))=chi(C)-chi(C')$. Если отображение $H(f)$ — изоморфизм, то в силу
  @prop:mapping-cone-homology комплекс $MC(f)$ ацикличен. Следовательно, из
  @cond:euler-homology-invariance вытекает, что $chi(MC(f))=0$. Отсюда
  заключаем, что $chi(C)=chi(C')$.
]

#theorem(title: [Гротендик])[
  #idx("теорема Гротендика")
  Пусть $bold(C)_0 subset bold(C)$ — допустимые подкатегории абелевой категории,
  причем каждый объект категории $bold(C)$ обладает конечной
  $bold(C)_0$-резольвентой. Тогда вложение $bold(C)_0 subset bold(C)$ индуцирует
  изоморфизм групп $K_0 (bold(C)_0) -> K_0 (bold(C))$.
] <th:grothendieck-resolution-k0>

#source(321)Начнем с доказательства леммы.

#lemma[
  Пусть $f:A' -> A$ — морфизм категории $bold(C)$ и $C arrow.r^epsilon A$ —
  конечная $bold(C)_0$-резольвента. Тогда существуют конечная
  $bold(C)_0$-резольвента $C' arrow.r^(epsilon') A'$ и морфизм $F:C' -> C$,
  накрывающий $f$.
] <lem:finite-resolution-morphism-lift>

#proof[
  Пусть $B=Ker (C_0 plus.o A' arrow.r^((epsilon,-f)) A)$ — расслоенное
  произведение для $C_0 arrow.r^epsilon A arrow.l^f A'$. Выберем эпиморфизм
  $C'_0 -> B$, где $C'_0 in bold(C)_0$. Определим $epsilon'$ и $F_0$ так, чтобы
  диаграмма
  $ #resolution-fiber() $
  была коммутативной. Так как отображение $epsilon$ сюръективно, то сюръективно
  и отображение $epsilon'$. Предположим теперь, что мы построили коммутативную
  диаграмму
  $ #resolution-induction() $
  строки которой точны и все $C'_i in bold(C)_0$. Тогда, как мы уже отмечали в
  начале этого параграфа, $Z_(n-1)$ и $Z'_(n-1)$ ($=Ker (d'_(n-1))$) лежат в
  $bold(C)$. Таким образом, можно применить указанную выше конструкцию и
  получить коммутативную диаграмму
  $ #resolution-kernel-step() $
  с точными строками. В конце концов мы получим, что $C_n=0$, т. е. мы завершим
  построение комплекса $C'$, используя конечную $bold(C)_0$-резольвенту объекта
  $Z'_(n-1)$, что и требовалось доказать.
]

#proof(head: [Доказательство теоремы @th:grothendieck-resolution-k0.])[
  Пусть $C -> A$ и $C' -> A$ — две конечные $bold(C)_0$-резольвенты объекта
  $A in bold(C)$. Применим лемму к резольвенте $C plus.o C' -> A plus.o A$ и к
  диагональному отображению $A -> A plus.o A$. В результате мы получим конечную
  $bold(C)_0$-резольвенту $C'' -> A$ и морфизмы $C'' -> C$ и $C'' -> C'$, оба
  #source(322)накрывающие морфизм $1_A$. Другими словами, можно рассматривать
  $1_A$ как индуцированное отображение гомологии $A=H(C'') -> H(C)=A$ и
  аналогично для $C'' -> C'$. Следовательно, из
  @prop:euler-characteristic-identities @cond:euler-mapping-cone вытекает, что
  $ chi^(bold(C)_0) (C)=chi^(bold(C)_0) (C'')=chi^(bold(C)_0) (C'). $
  Это показывает, что $A mapsto chi^(bold(C)_0) (C)$, где $C -> A$ — конечная
  $bold(C)_0$-резольвента, является корректно определенным отображением
  $r: ob bold(C) -> K_0 (bold(C)_0)$.

  Пусть $0 -> A' arrow.r^i A arrow.r^j A'' -> 0$ — точная последовательность в
  категории $bold(C)$ и $C -> A$ — конечная $bold(C)_0$-резольвента. Используя
  лемму, получаем коммутативную диаграмму
  $ #resolution-lift-square() $
  где $C' -> A'$ — конечная $bold(C)_0$-резольвента. Рассмотрим гомологическую
  последовательность #[@prop:mapping-cone-homology]:
  $ dots H_1 (C) -> H_1 (MC(I)) -> H_0 (C') -> H_0 (C) -> H_0 (MC(I)) -> dots. $
  Так как комплексы $C$ и $C'$ являются резольвентами, то $H_n (C)=0=H_n (C')$
  при $n!=0$ и $(H_0 (C') -> H_0 (C))=(A' arrow.r^i A)$ — мономорфизм, коядро
  которого совпадает с $A''$. Так как $MC(I)$ — конечный положительный комплекс
  в $bold(C)_0$, то из рассмотрения гомологической последовательности выводим,
  что $MC(I)$ — конечная $bold(C)_0$-резольвента объекта $Coker (i)=A''$. Таким
  образом,
  $
    r A''=chi^(bold(C)_0) (MC(I))=chi^(bold(C)_0) (C)-chi^(bold(C)_0) (C')
    =#[@prop:euler-characteristic-identities @cond:euler-mapping-cone]=r A-r A'.
  $
  Отсюда следует, что $r$ индуцирует гомоморфизм
  $r:K_0 (bold(C)) -> K_0 (bold(C)_0)$. Если $A in bold(C)_0$, то комплекс с
  одним объектом $A$ в нулевой степени является конечной
  $bold(C)_0$-резольвентой, поэтому и $r[A]_(bold(C))=[A]_(bold(C)_0)$. С другой
  стороны, если $A in bold(C)$ и $C$ — конечная $bold(C)_0$-резольвента, то
  рассмотрим конечный ацикличный комплекс $dots C_n -> dots -> C_0 -> A -> 0$.
  Используя @prop:euler-characteristic-identities
  @cond:euler-homology-invariance, видим, что $chi^bold(C)(C)=[A]_(bold(C))$.
  Так как $r[A]_(bold(C))=chi^(bold(C)_0) (C)$, то отображение
  $K_0 (bold(C)_0) -> K_0 (bold(C))$ переводит $r[A]_(bold(C))$ в
  $chi^bold(C)(C)=[A]_(bold(C))$. Это показывает, что отображение $r$ является
  обратным для отображения $K_0 (bold(C)_0) -> K_0 (bold(C))$, что доказывает
  теорему.
]

#theorem[
  Пусть $bold(P) subset bold(C)_0 subset bold(C)$ — допустимые подкатегории
  абелевой категории, $F$ — точный допустимый функтор на $bold(C)$ и $F_0$ — его
  ограничение на подкатегорию $bold(C)_0$. Допустим, что для каждого объекта
  $A in bold(C)$ выполнены следующие условия:
  #condition-list[
    #condition-item[если $alpha,beta in Aut_(bold(C)) (A,F)$ (и поэтому
      $F alpha=1_(F A)=F beta$), то существует эпиморфизм $C_0 -> A$, где
      $C_0 in bold(P)$, а $alpha$ и $beta$ поднимаются до автоморфизмов из
      группы $Aut_(bold(C)_0) (C_0,F_0)$;] <cond:relative-resolution-pair-lifts>

    #source(323)#condition-item[если $C -> A$ есть $bold(P)$-резольвента, то
      $Z_n (C) in bold(C)_0$ для некоторого $n>0$.]
    <cond:relative-resolution-termination>
  ]
  Тогда вложение $bold(C)_0 subset bold(C)$ индуцирует изоморфизм
  $K_1 (bold(C)_0,F_0) -> K_1 (bold(C),F)$.
] <th:relative-resolution-k1>

#proof[
  Пусть $(A,alpha) in Ker Sigma F$. Напомним, что $Ker Sigma F$ — полная
  подкатегория категории $Sigma bold(C)$, состоящая из объектов $(A,alpha)$, для
  которых $F alpha=1_(F A)$. В силу @cond:relative-resolution-pair-lifts можно
  найти точную последовательность в $Sigma bold(A)$
  $ 0 -> (Z_0,beta) -> (C_0,gamma_0) -> (A,alpha) -> 0, $
  где $C_0 in bold(P)$ и $F gamma_0=1_(F C_0)$, т. е.
  $(C_0,gamma_0) in Ker Sigma F_0$. Поскольку подкатегория $bold(C)$ допустимая,
  то $Z_0 in bold(C)$. Так как функтор $F$ точный и $F gamma_0=1_(F C_0)$, то
  $F beta=F gamma_0|_(F Z_0)=1_(F Z_0)$. Следовательно,
  $(Z_0,beta) in Ker Sigma F$. Таким образом, можно повторять этот процесс и
  получить $Ker (Sigma F_0)$-резольвенту: $(C,gamma) -> (A,alpha)$, где $C -> A$
  есть $bold(P)$-резольвента. Она не обязана быть конечной, но из нашего условия
  @cond:relative-resolution-termination следует, что ее можно оборвать на
  некотором месте, если необходимо заменить ее конечной резольвентой. В силу
  @cond:relative-resolution-pair-lifts для $alpha,alpha' in Aut_(bold(C)) (A,F)$
  можно с помощью описанной процедуры построить конечные
  $Ker (Sigma F_0)$-резольвенты $(C,gamma) -> (A,alpha)$ и
  $(C,gamma') -> (A,alpha')$ (в каждом из случаев используя один и тот же
  комплекс $C$).

  Если $(C,gamma) -> (A,alpha)$ — такая резольвента, то положим
  $r(A,alpha)=chi(C, gamma)=sum_n (-1)^n [C_n,gamma_n] in K_1 (bold(C)_0,F_0)$.
  Из доказательства теоремы @th:grothendieck-resolution-k0 следует, что
  отображение $r$ аддитивно на точных последовательностях. Если
  $(C,gamma') -> (A,alpha')$ — рассмотренная резольвента объекта $(A,alpha')$,
  то $(C,gamma gamma') -> (A,alpha alpha')$, очевидно, конечная
  $Ker (Sigma F_0)$-резольвента. Поэтому
  $
    r(A,alpha alpha')=chi(C, gamma gamma')=sum_n (-1)^n [C_n,gamma_n gamma'_n]
    =sum_n (-1)^n ([C_n,gamma_n]+[C_n,gamma'_n])=r(A,alpha)+r(A,alpha').
  $
  Следовательно, $r$ индуцирует гомоморфизм
  $K_1 (bold(C),F) -> K_1 (bold(C)_0,F_0)$. Точно так же, как в доказательстве
  теоремы @th:grothendieck-resolution-k0, мы убеждаемся, что этот гомоморфизм
  является обратным к гомоморфизму $K_1 (bold(C)_0,F_0) -> K_1 (bold(C),F)$, что
  и требовалось доказать.
]

Укажем теперь некоторые ситуации, в которых выполнено предположение
@cond:relative-resolution-pair-lifts теоремы @th:relative-resolution-k1.

#proposition[
  Пусть $bold(A)$ — абелева категория.
  #condition-list[
    #condition-item(format: "cyrillic")[Пусть $F$ — аддитивный функтор на
      категории $bold(A)$ и $f:P -> A$ — такой эпиморфизм в категории $bold(A)$,
      что каждый эндоморфизм $h in End_(bold(A)) (A)$, для которого $F h=0$,
      поднимается до эндоморфизма $h' in End_(bold(A)) (P)$, обладающего тем
      свойством, что $F h'=0$ (например, это так, если объект $P$ проективный и
      $F=0$). Пусть #source(324)$(f,0):Q=P plus.o P -> A$. Тогда каждый
      автоморфизм $alpha in Aut_(bold(A)) (A)$, для которого $F alpha=1_(F A)$,
      поднимается до автоморфизма $alpha' in Aut_(bold(A)) (Q)$, такого, что
      $F alpha'=1_(F Q)$.]
    <cond:automorphism-endomorphism-lift>

    #condition-item(format: "cyrillic")[Пусть $f_1:P_1 -> A_1$ и
      $f_2:P_2 -> A_2$ — эпиморфизмы в категории $bold(A)$, $Q=P_1 plus.o P_2$ —
      проективный объект, $(f_1,0):Q -> A_1$ и $(0,f_2):Q -> A_2$. Тогда любой
      изоморфизм $alpha:A_1 -> A_2$ поднимается до изоморфизма $alpha':Q -> Q$.]
    <cond:projective-isomorphism-lift>
  ]
] <prop:projective-automorphism-lifts>

#proof[
  @cond:automorphism-endomorphism-lift В группе
  $Aut_(bold(A)) (A plus.o A)=GL_2 (End_(bold(A)) (A))$
  справедливы следующие равенства:
  $
    mat(alpha, 0; 0, alpha^(-1))=
    mat(1, 0; 1, 1) mat(1, 0; alpha^(-1)-1, 1) mat(1, 1-alpha; 0, 1)
    mat(1, 0; -1, 1) mat(1, 1-alpha^(-1); 0, 1),
  $
  <eq:automorphism-diagonal-factorization>
  $ mat(0, -1; 1, 0)=mat(1, 0; 1, 1) mat(1, -1; 0, 1) mat(1, 0; 1, 1). $
  <eq:exchange-matrix-factorization>
  Так как $F alpha=1_(F A)$, то в силу предположения можно поднять $1-alpha$ и
  $1-alpha^(-1)$ до эндоморфизмов объекта $P$, обращающихся в нуль при $F$.
  Таким образом, при $f plus.o f:Q -> A plus.o A$ можно поднять
  $alpha plus.o alpha^(-1)$ до автоморфизма $alpha'$, представимого в группе
  $GL_2 (End_(bold(A)) (P))$ в виде
  $
    mat(1, 0; 1, 1) mat(1, 0; h_1, 1) mat(1, h_2; 0, 1)
    mat(1, 0; -1, 1) mat(1, -h_1; 0, 1),
  $
  где $F h_1=0=F h_2$. Тогда $F alpha'=1_(F Q)$. При композиции
  $Q arrow.r^(f plus.o f) A plus.o A arrow.r^((1,0)) A$ можно, очевидно, сначала
  поднять $alpha$ до $alpha plus.o alpha^(-1)$, а затем, как и требовалось, до
  $alpha'$.

  @cond:projective-isomorphism-lift Используя то же самое рассуждение,
  достаточно найти изоморфизм $alpha'$, для которого диаграмма
  $ #projective-isomorphism-lift() $
  коммутативна, поскольку нижний прямоугольник заведомо коммутативен. Используя
  изоморфизм $alpha plus.o 1_(A_2):A_1 plus.o A_2 -> A_2 plus.o A_2$, #source(
    325,
  )убеждаемся, что верхняя часть диаграммы изоморфна диаграмме
  $ #projective-isomorphism-lift(transformed: true) $
  Так как $P_i$ — проективные объекты, то существуют гомоморфизмы $h_1$ и $h_2$,
  для которых диаграмма
  $ #projective-inverse-lifts() $
  коммутативна. Используя формулу @eq:exchange-matrix-factorization, можно
  поднять $mat(0, -1_(A_2); 1_(A_2), 0)$ до
  $
    mat(1_(P_1), 0; h_1, 1_(P_2)) mat(1_(P_1), -h_2; 0, 1_(P_2))
    mat(1_(P_1), 0; h_1, 1_(P_2)).
  $
  Это показывает, что $mat(0, -alpha^(-1); alpha, 0)$ также можно поднять до
  изоморфизма. Это завершает доказательство утверждения
  @cond:projective-isomorphism-lift.
]

#theorem[
  Пусть $bold(C)_0 subset bold(C)$ — допустимые подкатегории абелевой категории.
  Допустим, что для любого объекта $A in bold(C)$ выполнены следующие условия:
  #condition-list[
    #condition-item[существует эпиморфизм $f:P_0 -> A$, где $P_0$ — проективный
      объект категории $bold(C)_0$;] <cond:projective-resolution-epimorphism>

    #condition-item[если $P -> A$ — резольвента объекта $A$, состоящая из
      проективных объектов категории $bold(C)_0$, то $Z_n (P) in bold(C)_0$ для
      некоторого $n>0$.] <cond:projective-resolution-termination>
  ]
  В этом случае вложение $bold(C)_0 subset bold(C)$ индуцирует изоморфизмы
  $K_i (bold(C)_0) -> K_i (bold(C))$ ($i=0,1$).

  Более общим образом, пусть $F$ — точный допустимый функтор на категории
  $bold(C)$ и $F_0$ — его ограничение на $bold(C)_0$. Допустим, что в
  приведенном условии @cond:projective-resolution-epimorphism $f$ можно выбрать
  так, что любой эндоморфизм $h in End_(bold(C)) (A)$, для которого $F h=0$,
  можно поднять до эндоморфизма $h' in End_(bold(C)) (P_0)$, такого, что
  $F h'=0$. Тогда отображение $K_1 (bold(C)_0,F_0) -> K_1 (bold(C),F)$ также
  является изоморфизмом.
] <th:projective-resolution-k-isomorphisms>

#proof[
  Из условий @cond:projective-resolution-epimorphism и
  @cond:projective-resolution-termination, конечно, следует, что каждый объект
  $A in bold(C)$ обладает $bold(C)_0$-резольвентой, и поэтому в силу теоремы
  @th:grothendieck-resolution-k0 отображение $K_0 (bold(C)_0) -> K_0 (bold(C))$
  является #source(326)изоморфизмом. Для доказательства того, что отображение
  $K_1 (bold(C)_0,F_0) -> K_1 (bold(C),F)$ — изоморфизм, надо лишь проверить
  выполнение предположений теоремы @th:relative-resolution-k1, где в качестве
  $bold(P)$ следует рассмотреть полную подкатегорию проективных объектов
  категории $bold(C)_0$. Заметим, что условия
  @cond:relative-resolution-termination теоремы @th:relative-resolution-k1 и
  @cond:projective-resolution-termination данной теоремы тождественны. Условие
  @cond:relative-resolution-pair-lifts теоремы @th:relative-resolution-k1
  является непосредственным следствием сделанных предположений и части
  @cond:automorphism-endomorphism-lift предложения
  @prop:projective-automorphism-lifts. Изоморфизм
  $K_1 (bold(C)_0) -> K_1 (bold(C))$ соответствует тому случаю, когда функтор
  $F$ нулевой. Тогда дополнительное предположение о поднятии эндоморфизмов,
  аннулируемых функтором $F$, выполняется автоматически, что и требовалось
  доказать.
]

В завершение приведем аналогичный результат об относительных группах.

#proposition[
  Пусть диаграмма точных допустимых функторов допустимых подкатегорий абелевых
  категорий
  $ #relative-resolution-functors() $
  коммутативна. Допустим, что выполнены условия
  @cond:projective-resolution-epimorphism и
  @cond:projective-resolution-termination теоремы
  @th:projective-resolution-k-isomorphisms для $bold(C)_0 subset bold(C)$ и что
  функтор $F$ переводит проективные объекты категории $bold(C)_0$ в проективные
  объекты категории $bold(C)'_0$. Тогда включение
  $italic("co")(F_0) subset italic("co")(F)$ индуцирует изоморфизм
  $K'_0 (F_0) -> K'_0 (F)$.
] <prop:relative-projective-resolution-k0>

#proof[
  Пусть $(A_1,alpha_1,A_2) in italic("co")(F)$. Выберем эпиморфизмы
  $f_i:P_i -> A_i$, где $P_i$ — проективные объекты в категории $bold(C)_0$
  ($i=1,2$). Пусть $Q=P_1 plus.o P_2$ и $(f_1,0):Q -> A_1$, $(0,f_2):Q -> A_2$.
  Так как функтор $F$ точен и переводит проективные объекты в проективные, то
  объекты $F P_i$ проективны, а отображения $F f_i$ сюръективны ($i=1,2$). Далее
  из предложения @prop:projective-automorphism-lifts
  @cond:projective-isomorphism-lift следует существование изоморфизма
  $alpha'_1$, для которого диаграмма
  $ #relative-resolution-lift() $
  коммутативна. Таким образом, мы построили эпиморфизм
  $(Q,alpha'_1,Q) -> (A_1,alpha_1,A_2)$, где $Q$ — проективный объект из
  $bold(C)_0$. Повторив этот процесс для ядра и т. д., получим резольвенту
  $(C,gamma_1,C) -> (A_1,alpha_1,A_2)$, где $C$ — комплекс проективных объектов
  из $bold(C)_0$. Условие @cond:projective-resolution-termination теоремы
  @th:projective-resolution-k-isomorphisms позволяет нам оборвать эту
  резольвенту, #source(327)если необходимо получить конечную
  $italic("co")(F_0)$-резольвенту объекта $(A_1,alpha_1,A_2)$. Допустим, что нам
  дан также объект $(A_2,alpha_2,A_3) in italic("co")(F)$. Пусть
  $f_3:P_3 -> A_3$ — эпиморфизм. Тогда в нашей конструкции заменим $Q$ на
  $Q'=Q plus.o P_3$ и определим $Q' -> A_i$ ($i=1,2,3$) с помощью $(f_1,0,0)$,
  $(0,f_2,0)$ и $(0,0,f_3)$. Можно поднять $alpha_1$ до
  $alpha''_1=alpha'_1 plus.o 1_(F P_3)$. Аналогично можно поднять $alpha_2$ до
  автоморфизма $alpha'_2$ объекта $F(P_2 plus.o P_3)$ и затем до
  $alpha''_2=1_(F P_1) plus.o alpha'_2$, действующего на $F Q'$. Тогда мы
  получим эпиморфизмы $(Q',alpha''_1,Q') -> (A_1,alpha_1,A_2)$ и
  $(Q',alpha''_2,Q') -> (A_2,alpha_2,A_3)$. Если таким же образом изменить
  указанную выше процедуру, то в результате можно получить резольвенты
  $(C,gamma_1,C) -> (A_1,alpha_1,A_2)$ и $(C,gamma_2,C) -> (A_2,alpha_2,A_3)$.
  Обрывая каждую из них в одной и той же точке, можно далее считать, что они
  являются конечными $italic("co")(F_0)$-резольвентами. Тогда
  $(C,gamma_2 gamma_1,C)$ оказывается конечной $italic("co")(F_0)$-резольвентой
  объекта $(A_1,alpha_2 alpha_1,A_3)$.

  Для доказательства того, что отображение $K'_0 (F_0) -> K'_0 (F)$ является
  изоморфизмом, построим обратное отображение, при котором
  $r(A_1,alpha_1,A_2)=chi^(italic("co")(F_0))(C,gamma_1,C) in K'_0 (F_0)$, где
  $(C,gamma_1,C)$ — конечная $italic("co")(F_0)$-резольвента. Из доказательства
  теоремы @th:grothendieck-resolution-k0 следует, что функция $r$ аддитивна на
  точных последовательностях. Для $(A_2,alpha_2,A_3)$ построим, как и выше,
  согласованные резольвенты. Тогда
  $
    r(A_1,alpha_2 alpha_1,A_3)=chi(C, gamma_2 gamma_1, C)
    =chi(C, gamma_1, C)+chi(C, gamma_2, C)
    =r(A_1,alpha_1,A_2)+r(A_2,alpha_2,A_3).
  $
  Таким образом, на самом деле $r$ индуцирует гомоморфизм на $K'_0 (F)$ (см.
  @prop:relative-grothendieck-composition-presentation), который, как легко
  видеть, является требуемым обратным отображением (см. доказательство теоремы
  @th:grothendieck-resolution-k0).
]
