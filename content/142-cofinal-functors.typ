#import "main-defs.typ": Aut, Id, K, Ker, Tran, colim, idx, source, symbol-idx
#import "statements.typ": (
  condition-item, condition-list, corollary, definition, lemma, proof,
  proposition,
)

#heading(level: 2)[
  Кофинальные функторы и представление группы $K_1$ в виде предела прямого
  спектра
]
<sec:cofinal-functors>

Пусть $bold(A)$~— категория с произведением. Тогда множество $M(bold(A))$
классов изоморфных объектов $(A)$, где $A in bold(A)$, является коммутативной
полугруппой с операцией $(A) + (B) = (A perp B)$. Введем обозначения:
#symbol-idx($G(A)$, sort: "G(A)", group: "groups", order: 94)
$ G(A) = Aut_(bold(A)) (A) $
и
#symbol-idx($G((A))$, sort: "G((A))", group: "groups", order: 95)
$ G((A)) = G(A) slash [G(A), G(A)] $
(факторгруппа по коммутанту группы $G(A)$), где $A in bold(A)$. Последнее
обозначение оправдано тем, что два $bold(A)$-изоморфизма $A -> B$ индуцируют
изоморфизмы $G(A) -> G(B)$, отличающиеся на внутренний автоморфизм.
Следовательно, они индуцируют (один) и тот же изоморфизм $G((A)) -> G((B))$. Это
доказывает, что группа $G((A))$ действительно зависит лишь от $(A)$.

Более общим образом, пусть $F: bold(A) -> bold(A)'$~— сохраняющий произведение
функтор. Пусть
$
  G(A, F) = Aut_(bold(A)) (A, F)
  = Ker(Aut_(bold(A)) (A) -> Aut_(bold(A)') (F A))
$
и
$ G((A), F) = G(A, F) slash [G(A), G(A, F)]. $
Если $F$~— постоянный функтор, то легко получить определение, данное ранее.
Кроме того, группа $G((A), F)$, как и раньше, зависит лишь от $(A)$.

Объект $B in bold(A)$ индуцирует гомоморфизм групп
$ G(A, F) arrow.r^(perp B) G(A perp B, F), quad alpha |-> alpha perp 1_B, $
который в свою очередь индуцирует гомоморфизм
$ G((A), F) arrow.r^(perp B) G((A perp B), F). $
#source(285)Кроме того, очевидно, что гомоморфизм $perp(B perp C)$ из $G(A, F)$
в $G(A perp B perp C, F)$ является композицией $perp B$ и $perp C$. Из этого
следует, что сопоставление $(A) |-> G((A), F)$ является функтором
$ G: Tran(M(bold(A))) -> ("абелевы группы"), $
где $Tran(M(bold(A)))$~— категория трансляций на полугруппе $M$ (в смысле
главы~@ch:category-algebra, §~@sec:direct-limits).

#proposition[
  Естественные гомоморфизмы
  $ G(A, F) -> K_1 (bold(A), F) $
  (см. @prop:whitehead-stabilization-relations и приведенные выше определения)
  индуцируют изоморфизм
  $ phi: G_(arrow.r) = colim G((A), F) -> K_1 (bold(A), F). $
] <prop:whitehead-translation-colimit>

#proof[
  Если $alpha in G(A, F)$ и $beta in G(A)$, то в категории $Ker Sigma F$ (по
  которой строится группа $K_1 (bold(A), F)$) объекты $alpha$ и
  $beta^(-1) alpha beta$ изоморфны. Следовательно,
  $[alpha^(-1) beta^(-1) alpha beta] = [beta^(-1) alpha beta] - [alpha]
  = 0$ в $K_1 (bold(A), F)$, и поэтому отображение $G(A, F) -> K_1 (bold(A), F)$
  пропускается через факторгруппу $G((A), F) = G(A, F) slash [G(A), G(A, F)]$.

  Если $B in bold(A)$, то $[alpha perp 1_B] = [alpha]$, и поэтому рассмотренные
  отображения согласованы с направленной системой гомоморфизмов
  $G((A), F) -> G((A perp B), F)$. Таким образом, получаем нужное отображение
  $phi$, причем $phi$ сюръективно. Чтобы убедиться в том, что $phi$~—
  изоморфизм, достаточно показать, что отображение
  $alpha |-> chevron.l alpha chevron.r$, где $chevron.l alpha chevron.r$~— класс
  объекта $alpha$ в $G_(arrow.r)$, удовлетворяет аксиомам
  @ax:whitehead-isomorphism, @ax:whitehead-product и @ax:whitehead-composition
  для $K_1$. Действительно, из свойств универсальности для группы вытекает
  существование обратного отображения.

  Проверка аксиомы @ax:whitehead-isomorphism уже проведена, поскольку группа
  $G((A), F)$ зависит лишь от класса изоморфных объектов $(A)$ объекта $A$.
  Таким образом, если $(A, alpha) tilde.eq (B, beta)$ в $Ker Sigma F$, то
  элементы $alpha$, $beta$ отождествляются уже в группе $G((A), F)$ с
  использованием любого изоморфизма $A -> B$. Так как $G(A, F) -> G_(arrow.r)$~—
  гомоморфизм, то очевидно, что аксиома @ax:whitehead-composition выполняется.
  Наконец, для данных объектов $(A, alpha)$ и $(B, beta)$ надо установить, что
  $chevron.l alpha perp beta chevron.r = chevron.l alpha chevron.r
  + chevron.l beta chevron.r$. В силу определения направленной системы классы
  $chevron.l alpha chevron.r = chevron.l alpha perp 1_B chevron.r$ и
  $chevron.l beta chevron.r = chevron.l beta perp 1_A chevron.r
  = chevron.l 1_A perp beta chevron.r$ (в последнем равенстве использован
  изоморфизм $beta perp 1_A tilde.eq 1_A perp beta$). Следовательно,
  $chevron.l alpha perp beta chevron.r
  = chevron.l (alpha perp 1_B)(1_A perp beta) chevron.r
  = chevron.l alpha perp 1_B chevron.r + chevron.l 1_A perp beta chevron.r
  = chevron.l alpha chevron.r + chevron.l beta chevron.r$, что и требовалось
  доказать.
]

#corollary[
  Пусть $bold(A)_0$~— полная кофинальная подкатегория категории $bold(A)$ и
  $F_0 = F|_(bold(A)_0)$. Тогда функтор вложения индуцирует изоморфизм
  $ K_1 (bold(A)_0, F_0) -> K_1 (bold(A), F). $
] <cor:whitehead-cofinal-full-subcategory>

#proof[
  #source(286)Если $A, B in bold(A)_0$, то
  $Aut_(bold(A)_0) (A) = Aut_(bold(A)) (A)$ и $A tilde.eq B$ в
  $bold(A)_0 <=> A tilde.eq B$ в $bold(A)$ (поскольку подкатегория $bold(A)_0$
  полна в $bold(A)$). Таким образом, $M(bold(A)_0)$~— кофинальная подполугруппа
  в $M(bold(A))$. Кроме того, $K_1 (bold(A)_0, F_0) = G_(0, arrow.r)$, где
  $G_0$~— пересечение рассмотренной выше группы $G$ с
  $Tran M(bold(A)_0) subset Tran M(bold(A))$. В силу
  @prop:cofinal-translation-category индуцированное отображение
  $G_(0, arrow.r) -> G_(arrow.r)$ является изоморфизмом.
]

#corollary[
  Пусть $A_1, A_2, dots, A_n, dots$~— последовательность объектов из $bold(A)$.
  Положим $A_(n, m) = A_(n+1) perp dots.c perp A_m$ для $0 <= n < m$ и
  $S_n = A_(0, n)$. Допустим, что
  #condition-list[
    #condition-item[если $A in bold(A)$ и $n >= 0$, то существуют $B in bold(A)$
      и $m > n$, такие, что $A perp B tilde.eq A_(n, m)$.]
    <cond:whitehead-sequential-cofinality>
  ]
  Пусть $G(bold(A), F)$~— предел прямого спектра групп
  $G(S_n, F) = Aut_(bold(A)) (S_n, F)$ относительно гомоморфизмов
  $perp A_(n, m): G(S_n, F) -> G(S_m, F)$ для $n < m$. Пусть $G(bold(A))$~—
  соответствующий предел прямого спектра групп $G(S_n) = Aut_(bold(A)) (S_n)$.
  Тогда естественные гомоморфизмы $G(S_n, F) -> K_1 (bold(A), F)$ индуцируют
  изоморфизм
  $ G(bold(A), F) slash [G(bold(A)), G(bold(A), F)] -> K_1 (bold(A), F). $
] <cor:whitehead-sequential-group-colimit>

#proof[
  Объект, стоящий слева от стрелки, в точности равен пределу прямого спектра
  групп $G((S_n), F) = G(S_n, F) slash [G(S_n), G(S_n, F)]$ относительно
  гомоморфизмов $perp(A_(n, m))$ (в терминах введенных выше обозначений).
  Утверждение следствия непосредственно вытекает из
  @prop:whitehead-translation-colimit и @prop:sequential-cofinal-translations
  (условие~@eq:sequential-cofinal-condition в точности соответствует сделанному
  выше допущению~@cond:whitehead-sequential-cofinality). Следствие доказано.
]

#definition(upright: true)[
  Сохраняющий произведение функтор $F: bold(A) -> bold(A)'$ назовем #idx(
    "функтор E-сюръективный",
  )#idx("E-сюръективный функтор")_Е-сюръективным_, если для любого объекта
  $A in bold(A)$ и элемента $alpha'$ коммутанта группы $Aut_(bold(A)') (F A)$
  найдутся объект $B in bold(A)$ и элемент $alpha$ коммутанта группы
  $Aut_(bold(A)) (A perp B)$, для которых $F alpha = alpha' perp 1_(F B)$.
] <def:e-surjective-functor>

#proposition[
  Пусть $F: bold(A) -> bold(A)'$~— кофинальный функтор, сохраняющий
  произведение. Тогда группа $K_1 bold(A)'$ является пределом прямого спектра на
  $Tran(M(bold(A)))$ групп $G((F A))$, т. е. факторгрупп по коммутанту групп
  $G(F A) = Aut_(bold(A)') (F A)$, $(A) in bold(A)$ относительно морфизмов
  $G((F A)) -> G((F(A perp B)))$, индуцированных отображением
  $alpha |-> alpha perp 1_(F B)$ для $alpha in G(F A)$. Если функтор $F$
  является Е-сюръективным, то последовательность
  $ K_1 (bold(A), F) -> K_1 (bold(A)) -> K_1 (bold(A)') $
  точна. Если, кроме того, существует кофинальный функтор, сохраняющий
  произведение, $F': bold(A)' -> bold(A)$, для которого
  $F compose F' tilde.eq Id_(bold(A)')$, то эта точная последовательность
  расщепляется.
] <prop:relative-whitehead-image-kernel>

#proof[
  #source(287)В силу предложения~@prop:whitehead-translation-colimit
  $K_1 bold(A)' = G_(arrow.r)$, где отображение
  $G: Tran(M(bold(A)')) -> ("абелевы группы")$ определено так: $A' |-> G((A'))$.
  Так как функтор $F$ кофинален, то он индуцирует кофинальный гомоморфизм
  $M(F): M(bold(A)) -> M(bold(A)')$, а следовательно, и кофинальный функтор
  $Tran(M(F)): Tran(M(bold(A))) -> Tran(M(bold(A)'))$. В этой ситуации из
  @prop:cofinal-translation-category вытекает, что
  $(G compose Tran(M(F)))_(arrow.r) -> G_(arrow.r)$~— изоморфизм. Первая часть
  предложения и содержит в явном виде это утверждение.

  Предположим теперь, что функтор $F$ является Е-сюръективным и что
  $[A, alpha]_bold(A) in Ker K_1 F$. Нам надо показать, что
  $[A, alpha]_bold(A) = [B, beta]_bold(A)$ для такого $beta$, для которого
  $F beta = 1_(F B)$, т. е. это означает, что $(B, beta) in Ker Sigma F$.
  (Очевидно, и это отмечалось ранее, что композиция двух рассматриваемых
  отображений равна нулю.) В силу @prop:whitehead-commutator-stabilization можно
  выбрать $B' in bold(A)'$ так, что $F alpha perp 1_(B')$ лежит в коммутанте
  группы $Aut_(bold(A)') (F A perp B')$. Кофинальность функтора $F$ позволяет
  нам выбрать объект $B'$ в виде $F B$. Заменяя в случае необходимости объект
  $B$ еще раз и учитывая Е-сюръективность функтора $F$, найдем элемент $epsilon$
  коммутанта группы $Aut_(bold(A)) (A perp B)$, для которого
  $F epsilon = F alpha perp 1_(F B)$. Тогда
  $[alpha] = [alpha perp 1_B] + [epsilon^(-1)] = [beta]$ в $K_1 (bold(A))$, где
  элемент $beta = (alpha perp 1_B)epsilon^(-1)$ таков, что
  $F beta = 1_(F(A perp B))$. Это показывает, что последовательность точна.

  Из предложения~@prop:whitehead-translation-colimit и первой части этого
  предложения следует, что последовательность
  $ K_1 (bold(A), F) -> K_1 (bold(A)) -> K_1 (bold(A)') $
  является пределом прямого спектра последовательностей
  $ G((A), F) -> G((A)) -> G((F A)), quad A in bold(A), $
  которые являются факторизациями последовательностей
  $ G(A, F) -> G(A) -> G(F A). $
  Существование функтора $F'$, для которого $F compose F' tilde.eq
  Id_(bold(A)')$, влечет за собой тот факт, что последние последовательности
  являются расщепляемыми расширениями групп для кофинальных объектов
  $A = F' A'$. Следовательно, окончательное утверждение предложения вытекает из
  следующего утверждения:
]

#lemma[
  Пусть
  $ 1 -> N -> G arrow.r^p G' -> 1 $
  ~— расщепляемое расширение групп. Тогда последовательность
  $ 0 -> N slash [G, N] -> G slash [G, G] -> G' slash [G', G'] -> 0 $
  является расщепляемой короткой точной последовательностью абелевых групп.
] <lem:split-extension-abelianization>

#proof[
  #source(288)Если $h: G' -> G$ расщепляет $p$ (т. е. $p h = 1_(G')$), то надо
  лишь убедиться в том, что отображение $x |-> x(h p(x))^(-1)$ индуцирует
  гомоморфизм $G slash [G, G] -> N slash [G, N]$. Действительно, этот
  гомоморфизм расщепляет левую часть последовательности, в то время как $h$
  расщепляет правую часть. Положим $e = h p: G -> G$. Пусть $x, y in G$. Тогда
  $
    x y e(x y)^(-1) = x(e(x)^(-1)y e(y)^(-1)) times
    (e(y)y^(-1)e(x))y e(y)^(-1)e(x)^(-1)
    = (x e(x)^(-1))(y e(y)^(-1))((e(y)y^(-1)e(x) times
      (e(y)y^(-1))^(-1)e(x)^(-1))
    equiv (x e(x)^(-1))(y e(y)^(-1)) quad (mod [G, N]).
  $
  Это доказывает лемму.
]
