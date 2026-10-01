#import "main-defs.typ": (
  Coker, FiniteGroupCat, Frob, FrobModules, G, GroupCat, Im, K, Ker, idx,
  source, symbol-idx,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, definition, example, proof,
  proposition,
)
#import "diagrams/finite-group-induction-basic.typ": (
  frobenius-module-morphism, frobenius-morphism,
)

== Функторы Фробениуса и фробениусовы модули <sec:frobenius-functors-modules>

Для того чтобы аксиоматизировать изложение теорем индукции в следующих
параграфах, мы введем понятие _фробениусова функтора_#idx(
  "фробениусов функтор",
)#idx("функтор Фробениуса") на категории $bold(C)$. Это не что иное, как функтор
$G: bold(C) -> Frob$. Поэтому нам надо описать категорию
$ Frob. $
#symbol-idx($Frob$, sort: "Frob", group: "categories", order: 7)
Ее объектами являются коммутативные кольца. Морфизмом $A -> B$ в категории
$Frob$ является пара $(i_*,i^*)$ аддитивных отображений
$ #frobenius-morphism() $
таких, что $i^*$ — гомоморфизм колец и что
$ b dot i_* a=i_* (i^* b dot a) quad (a in A,b in B). $
<eq:frobenius-ring-reciprocity>
Если $(j_*,j^*)$ — другой морфизм, то
$ (j_*,j^*) (i_*,i^*)=(j_* dot i_*,i^* dot j^*). $
Проверим, что это допустимое отображение. Если $a in A$ и $c in C$, то
$ c dot j_* i_* a=j_* (j^* c dot i_* a)=j_* (i_* (i^* j^* c dot a)). $
Если $G$ и $G'$ — фробениусовы функторы на категории $bold(C)$, то можно
говорить о морфизме (т. е. естественном преобразовании) из $G$ в $G'$.

#example[
  Пусть $GroupCat$ — категория, объекты которой есть группы, а морфизмами
  являются мономорфизмы $j: pi' -> pi$, для которых индекс $[pi:j (pi')]$
  конечен. Пусть $R$ — коммутативное кольцо. Тогда из
  @prop:group-ring-induction-restriction следует, что
  $ G_R: GroupCat -> Frob, quad pi arrow.r.bar G_R (pi) $
  #symbol-idx($G_R$, sort: "G_R", group: "groups", order: 92)
  является фробениусовым функтором относительно гомоморфизмов (индукции и
  ограничения). Если $f: R' -> R$ — гомоморфизм коммутативных колец, то из
  @prop:group-ring-scalar-extension-restriction следует, что
  $f_*: G_(R') -> G_R$ является морфизмом фробениусовых функторов.
] <exm:group-ring-frobenius-functor>

#source(437)
Пусть $G: bold(C) -> Frob$ — фробениусов функтор. Тогда следующее образование
$K$ назовем _фробениусовым $G$-модулем_:#idx("фробениусов модуль")

#condition-list[
  #condition-item[$K$ сопоставляет каждому объекту $pi in bold(C)$
    $G (pi)$-модуль $K (pi)$;] <cond:frobenius-module-object>

  #condition-item[
    $K$ сопоставляет каждому морфизму $j: pi' -> pi$ в категории $bold(C)$ пару
    аддитивных отображений $K (j)=(j_*,j^*)$:
    $ #frobenius-module-morphism() $
  ] <cond:frobenius-module-morphism>
]

таких, что $j^*$ является $(j^*: G (pi) -> G (pi'))$-полулинейным отображением
(мы ради краткости пишем также $G (j)=(j_*,j^*)$), и таких, что
$
  j_* a' dot b=j_* (a' dot j^* b) quad (a' in G (pi'),b in K (pi)), \
  a dot j_* b'=j_* (j^* a dot b') quad (a in G (pi),b' in K (pi')).
$
<eq:frobenius-module-reciprocity>
Кроме того, мы требуем, чтобы каждое из отображений $j arrow.r.bar j_*$ и
$j arrow.r.bar j^*$ превращало $K$ соответственно в ковариантный и
контравариантный функтор. Фробениусовы $G$-модули как объекты сами образуют
категорию, которую мы обозначим через
$ FrobModules(G). $
#symbol-idx($FrobModules(G)$, sort: "mod-", group: "categories", order: 15)
Если $K,H in FrobModules(G)$, то морфизм $f: K -> H$ — это совокупность
$G (pi)$-гомоморфизмов $f (pi): K (pi) -> H (pi)$ $(pi in bold(C))$, являющихся
одновременно естественным преобразованием ковариантных и контравариантных
функторов, входящих в определение $K$ и $H$. Определим $K plus.o H$, полагая
$(K plus.o H) (pi)=K (pi) plus.o H (pi)$ и т. д. Это превращает $FrobModules(G)$
в _абелеву категорию_. Например, $Ker (f)$ существует и допускает прозрачное
описание $Ker (f) (pi)=Ker (f (pi))$, где морфизмы индуцированы отображениями
$j_*$ и $j^*$. Аналогично описываются $Coker (f)$, $Im (f)$ и т. д.

Тот факт, что категория $FrobModules(G)$ абелева, технически весьма полезен, как
мы увидим в следующих параграфах. В этом духе можно рассматривать фробениусовы
функторы на фиксированной категории $bold(C)$ как коммутативные кольца, а их
фробениусовы модули как модули над этими кольцами. Заметим, в частности, что
если $G' -> G$ — морфизм фробениусовых функторов, то он дает нам возможность
рассматривать фробениусовы $G$-модули как фробениусовы $G'$-модули (по
«ограничению»).

#example[
  Пусть $G_R: GroupCat -> Frob$ — фробениусов функтор из примера
  @exm:group-ring-frobenius-functor. Пусть $K_R$ — один из «базисных
  $G_R$-модулей» (см. @def:group-ring-frobenius-functor). Тогда из
  @prop:group-ring-induction-restriction следует, что $K_R$ является
  фробениусовым $G_R$-модулем. Если $f: R' -> R$ — гомоморфизм коммутативных
  колец, то из @prop:group-ring-scalar-extension-restriction следует, что
  отображение $f_*: K_(R') -> K_R$ оказывается
  $(f_*: G_(R') -> G_R)$-полулинейным. Эквивалентно, если рассматривать $K_R$
  как $G_(R')$-модуль в силу отображения $f_*$, то отображение
  $f_*: K_(R') -> K_R$ является #source(
    438,
  )$G_(R')$-гомоморфизмом. Таким образом, его ядро, коядро и т. д. также
  являются $G_(R')$-модулями.
] <exm:basic-frobenius-modules>

Через $FiniteGroupCat$#symbol-idx(
  $FiniteGroupCat$,
  sort: "FG",
  group: "categories",
  order: 5,
) обозначим полную подкатегорию конечных групп в $GroupCat$. Пусть $R$ —
коммутативное регулярное кольцо. Если $pi in FiniteGroupCat$, то из предложения
@prop:regular-group-ring-resolution следует, что
$ K_i (bold(M)_0 (R pi))=G_i (R pi) quad (i=0,1). $
С этими отождествлениями вложение $italic(P) (R pi) subset bold(M)_0 (R pi)$
индуцирует гомоморфизмы Картана
$ c_i (R pi): K_i (R pi) -> G_i (R pi) quad (i=0,1). $
Очевидно, что эти гомоморфизмы являются морфизмами фробениусовых модулей над
функтором $G_R: FiniteGroupCat -> Frob$. Таким образом, как и выше, их ядра,
коядра и т. д. также являются фробениусовыми $G_R$-модулями.

#definition[
  Пусть $C$ — класс объектов в категории $bold(C)$, $G: bold(C) -> Frob$ —
  фробениусов функтор и $K in FrobModules(G)$. Тогда для каждой группы
  $pi in bold(C)$ определим
  $ K_C (pi)=sum Im j_* $
  и
  $ K^C (pi)=inter.big Ker (j^*), $
  где $j$ пробегает все морфизмы $j: pi' -> pi$ с $pi' in C$ и где
  $K (j)=(j_*,j^*)$.
] <def:frobenius-induction-restriction-subgroups>

#proposition[
  В обозначениях определения @def:frobenius-induction-restriction-subgroups
  получаем

  #condition-list[
    #condition-item(format: "cyrillic")[
      $G (pi) K_C (pi)+G_C (pi) K (pi) subset K_C (pi)$ и
      $G (pi) K^C (pi)+G^C (pi) K (pi) subset K^C (pi)$.
    ] <cond:frobenius-subgroup-absorption>

    #condition-item(format: "cyrillic")[
      $K_C (pi)$ и $K^C (pi)$ являются $G (pi)$-подмодулями в $K (pi)$.
    ] <cond:frobenius-subgroups-module-closure>

    #condition-item(format: "cyrillic")[
      $G^C (pi) K_C (pi)=0=G_C (pi) K^C (pi)$.
    ] <cond:frobenius-subgroup-annihilation>

    #condition-item(format: "cyrillic")[
      Если $f: K -> H$ — морфизм фробениусовых $G$-модулей, то
      $f (pi) (K_C (pi)) subset H_C (pi)$ и $f (pi) (K^C (pi)) subset H^C (pi)$.
    ] <cond:frobenius-subgroups-functoriality>

    #condition-item(format: "cyrillic")[
      Если $j^* (K_C (pi)) subset K_C (pi')$ (соответственно
      $j_* (K^C (pi')) subset K^C (pi)$) для каждого морфизма $j: pi' -> pi$
      категории $bold(C)$, то $K_C$ (соответственно $K^C$) — фробениусов
      $G$-модуль.
    ] <cond:frobenius-submodule-reciprocity>
  ]
] <prop:frobenius-subgroups-properties>

#proof[
  @cond:frobenius-subgroup-absorption Допустим, что $j: pi' -> pi$ — морфизм и
  $pi' in C$. Если $a in G (pi)$ и $b' in K (pi')$, то
  $a dot j_* b'=j_* (j^* a dot b')$. Поэтому $G (pi) K_C (pi) subset K_C (pi)$.
  Аналогично если $a' in G (pi')$ и $b in K (pi)$, то
  $j_* a' dot b=j_* (a' dot j^* b)$. Поэтому $G_C (pi) K (pi) subset K_C (pi)$,
  что доказывает первую часть утверждения @cond:frobenius-subgroup-absorption.
  Отображения $j^*$ являются $G$-полулинейными в том смысле, что
  $j^* (a dot b)=j^* a dot j^* b$ для $a in G (pi)$ и $b in K (pi)$. Из этого
  немедленно следует последняя часть утверждения
  @cond:frobenius-subgroup-absorption.

  @cond:frobenius-subgroups-module-closure Непосредственно вытекает из
  @cond:frobenius-subgroup-absorption.

  #source(439)@cond:frobenius-subgroup-annihilation Если $j$ выбрано, как и
  выше, то пусть $a in G (pi),a' in G (pi'),b in K (pi),b' in K (pi')$. Тогда
  $j_* a' dot b=j_* (a' dot j^* b)$ и $a dot j_* b'=j_* (j^* a dot b')$. Таким
  образом, если $b in Ker (j^*)$ и $a in Ker (j^*)$, то
  $j_* a' dot b=0=a dot j_* b'$, что доказывает утверждение
  @cond:frobenius-subgroup-annihilation.

  @cond:frobenius-subgroups-functoriality Утверждение следует из
  перестановочности $f$ с $j_*$ и $j^*$.

  @cond:frobenius-submodule-reciprocity Немедленно вытекает из определений,
  поскольку если $j: pi' -> pi$ — морфизм в категории $bold(C)$, то $j_*$
  сохраняет $K_C$ и $j^*$ сохраняет $K^C$. Таким образом, если допустить далее,
  что $j^*$ сохраняет $K_C$ (соответственно $j_*$ сохраняет $K^C$), то
  $pi arrow.r.bar K_C (pi)$ (соответственно $pi arrow.r.bar K^C (pi)$)
  превращается в бифунктор, значение которого на $pi$ является $G (pi)$-модулем
  (в силу части @cond:frobenius-subgroups-module-closure). Формула взаимности
  Фробениуса, требующая, чтобы $K_C$ (соответственно $K^C$) являлся бы
  $G$-модулем, имеет место, поскольку она выполнена в $K$, что и требовалось
  доказать.
]

#definition[
  Пусть $e$ — натуральное число. Будем говорить, что _экспонента группы $pi$
  равна $e$_,#idx("экспонента группы") если порядок каждого элемента группы $pi$
  делит число $e$ (т. е. $x^e=1$ для всех $x in pi$, если $pi$ —
  мультипликативная группа, или $e x=0$ для всех $x in pi$, если $pi$ —
  аддитивная группа). Множество экспонент (если оно непусто) оказывается
  множеством неотрицательных элементов некоторого идеала кольца $ZZ$. Через
  $ exp (pi) $
  #symbol-idx($exp$, sort: "exp", group: "operators", order: 46)
  мы обозначим наименьшую экспоненту группы (если она существует). Если $A$ —
  абелева группа и $I$ — подгруппа, то будем говорить, что _экспонента подгруппы
  $I$ в $A$ равна $e$_,#idx("экспонента подгруппы") если экспонента группы
  $A slash I$ равна $e$. Если $A$ — кольцо и $I$ — двусторонний идеал, то это
  равносильно тому, что характеристика кольца $A slash I$ делит число $e$, т. е.
  что $e dot 1 in I$.
] <def:group-exponent>

#proposition(title: [«принципы индукции и ограничения»])[
  #idx("принципы индукции и ограничения")
  Пусть $G: bold(C) -> Frob$ — фробениусов функтор, $C$ — класс объектов в
  $bold(C)$ и объект $pi in bold(C)$ таков, что экспонента $G_C (pi)$ в группе
  $G (pi)$ равна $e$. Тогда для всех фробениусовых $G$-модулей $K$ экспоненты
  групп $K (pi) slash K_C (pi)$ и $K^C (pi)$ равны $e$.
] <prop:frobenius-induction-restriction-principles>

#proof[
  Используя
  @prop:frobenius-subgroups-properties@cond:frobenius-subgroup-absorption,
  получаем, что $e K (pi)=e G (pi) K (pi) subset G_C (pi) K (pi)
  subset K_C (pi)$. Используя
  @prop:frobenius-subgroups-properties@cond:frobenius-subgroup-annihilation,
  получаем $e K^C (pi)=e G (pi) K^C (pi) subset G_C (pi) K^C (pi)=0$, что и
  требовалось доказать.
]

#corollary[
  Сохраним обозначения и предположения предложения
  @prop:frobenius-induction-restriction-principles. Через $C_pi$ обозначим
  множество объектов $pi' in C$, для которых существует морфизм $pi' -> pi$.
  Предположим, что группа $K (pi')$ периодическая (соответственно экспоненты
  $d$) для всех #source(440)$pi' in C_pi$. Тогда группа $K (pi)$ периодическая
  (соответственно экспоненты $d e$).
] <cor:frobenius-induction-torsion>

#proof[
  Из предположений следует, что группа $K_C (pi)$ периодическая (соответственно
  экспоненты $d$). В силу @prop:frobenius-induction-restriction-principles
  экспонента группы $K (pi) slash K_C (pi)$ равна $e$. Утверждение следствия
  немедленно вытекает из этого.
]

#corollary[
  Сохраним обозначения и предположения предложения
  @prop:frobenius-induction-restriction-principles. Пусть $f: K -> H$ — морфизм
  фробениусовых $G$-модулей. Допустим, что группа $K (pi)$ без кручения и что
  для всех $pi' in C_pi$ группа $Ker (f (pi'))$ периодическая (например, что
  $f (pi')$ является мономорфизмом). Тогда $f (pi)$ — мономорфизм.
] <cor:frobenius-torsion-free-injectivity>

#proof[
  В силу следствия @cor:frobenius-induction-torsion, примененного к $Ker (f)$,
  группа $Ker (f (pi))$ периодическая. Так как группа $K (pi)$ без кручения, то
  из этого следует, что $Ker (f (pi))=0$, а это и требовалось доказать.
]
