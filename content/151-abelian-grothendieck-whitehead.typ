#import "main-defs.typ": Ex, Int, K, idx, ob, source, symbol-idx
#import "statements.typ": (
  condition-item, condition-list, definition, named-axiom,
)
#import "diagrams/abelian-k-theory-exact.typ": exact-quotient-square

== Группы Гротендика и Уайтхеда в абелевых категориях
<sec:abelian-grothendieck-whitehead>

Все категории в этой главе будут удовлетворять приведенным ниже условиям, хотя
условие @cond:admissible-kernel-closure будет существенным лишь начиная с
§~@sec:devissage.

#definition[
  Подкатегория $bold(C)$ абелевой категории $bold(A)$ будет называться
  _допустимой_,#idx("допустимая подкатегория") если она удовлетворяет следующим
  условиям:
  #condition-list[
    #condition-item(format: "cyrillic")[$bold(C)$ — полная подкатегория в
      категории $bold(A)$, содержащая нулевой
      объект;] <cond:admissible-full-zero>
    #condition-item(format: "cyrillic")[классы изоморфных объектов категории
      $bold(C)$ образуют множество;] <cond:admissible-small-isomorphism-classes>
    #condition-item(format: "cyrillic")[все конечные прямые суммы объектов
      категории $bold(C)$ снова принадлежат
      $bold(C)$;] <cond:admissible-direct-sums>
    #condition-item(format: "cyrillic")[если $0 -> A' -> A -> A'' -> 0$ —
      короткая точная последовательность в категории $bold(A)$ и
      $A,A'' in bold(C)$, то $A' in bold(C)$.] <cond:admissible-kernel-closure>
  ]
] <def:admissible-abelian-subcategory>

Очевидно, что в этом случае категория $Sigma bold(C)$ ($=bold(C)^Int$, см.
@def:whitehead-group) является допустимой подкатегорией в абелевой категории
$Sigma bold(A)$. Назовем объект $P$ _проективным_ в $bold(C)$,#idx(
  "проективный объект",
) если $P in bold(C)$ и $P$ — проективный объект категории $bold(A)$. Аналогично
назовем последовательность в категории $bold(C)$ _точной_,#idx(
  "точная последовательность",
) если она точна в категории $bold(A)$. Категорию коротких точных
последовательностей $0 -> A' -> A -> A'' -> 0$ категории $bold(C)$ обозначим
через
$ Ex (bold(C)) quad (subset Ex (bold(A))). $
#symbol-idx($Ex$, sort: "Ex", group: "operators", order: 45)

Назовем категорию $bold(C)$ _полупростой_,#idx("полупростая категория") если все
короткие точные последовательности в $bold(C)$ расщепляются. Заметим, что из
этого не следует, что все объекты категории $bold(C)$ полупросты. Из этого также
не следует, что категория $Sigma bold(C)$ полупростая.

Пусть $bold(C) subset bold(A)$ и $bold(C)' subset bold(A)'$ — допустимые
подкатегории абелевых категорий. Функтор $F: bold(C) -> bold(C)'$ назовем
_допустимым_,#idx("допустимый функтор")#idx("функтор допустимый") если он
индуцирован аддитивным функтором $overline(F): bold(A) -> bold(A)'$. Будем
называть функтор $F$ _точным_,#idx("точный функтор")#idx("функтор точный") если
он переводит короткие точные последовательности категории $bold(C)$ в короткие
точные последовательности категории $bold(C)'$. В этом случае функтор $F$
индуцирует аддитивный функтор
$ Ex (F): Ex (bold(C)) -> Ex (bold(C)'). $
#source(310)Кроме того, функтор $Sigma F: Sigma bold(C) -> Sigma bold(C)'$
точный, если точен функтор $F$. Категория $italic("co")(F)$ является аддитивной
категорией. Если функтор $overline(F)$ точный, то категория
$italic("co")(overline(F))$ оказывается абелевой категорией, содержащей
допустимую подкатегорию $italic("co")(F)$.
#symbol-idx($italic("co")$, sort: "co", group: "operators", order: 34)

Наличие операции прямой суммы $plus.o$ позволяет рассматривать $bold(C)$ как
категорию с произведением (в смысле гл.~@ch:exact-k-sequences). Кроме того,
любой аддитивный функтор сохраняет произведение. Желая избежать неточностей,
через
$ (bold(C),plus.o) $
обозначим категорию $bold(C)$ с произведением. Таким образом, можно рассмотреть
группы
$ K_i (bold(C),plus.o) quad (i=0,1), $
построенные в последней главе. Аналогично, если функтор $F: bold(C) -> bold(C)'$
допустимый, рассмотрим группы
$ K'_0 (F,plus.o) quad "и" quad K_1 (F,plus.o), $
построенные как факторгруппы группы $K_i (italic("co")(F),plus.o)$. Введем
теперь группы $K_i (bold(C))$ ($i=0,1$) и группу $K'_0 (F)$ как факторгруппы
соответствующих рассмотренных выше групп. Они получаются с учетом следующего
требования: класс объекта в $K$ должен быть аддитивной функцией не только
относительно прямых сумм, но и относительно всех коротких точных
последовательностей. Именно функция
$ [quad ]_(bold(C)): ob bold(C) -> K_0 (bold(C)) $
универсальна относительно отображений в абелеву группу, удовлетворяющих условию
#named-axiom[
  Если $(0 -> A' -> A -> A'' -> 0) in Ex (bold(C))$, то
  $ [A]_(bold(C))=[A']_(bold(C))+[A'']_(bold(C)). $
] <ax:abelian-k0-additivity>
Аналогично функция
$ [quad ]_(bold(C)): ob Sigma bold(C) -> K_1 (bold(C)) $
универсальна относительно отображений в абелеву группу, удовлетворяющих условию
@ax:abelian-k0-additivity и условию #named-axiom[
  Если $(A,alpha),(A,beta) in Sigma bold(C)$, то
  $ [A,alpha beta]_(bold(C))=[A,alpha]_(bold(C))+[A,beta]_(bold(C)). $
] <ax:abelian-k1-composition>

Если функтор $F: bold(C) -> bold(C)'$ точный, то функция
$ [quad ]_F: ob italic("co")(F) -> K'_0 (F) $
универсальна относительно отображений в абелеву группу, удовлетворяющих
следующим условиям:
#source(311)
#named-axiom[
  Если последовательность
  $(0 -> (A'_1,alpha',A'_2) -> (A_1,alpha,A_2) -> (A''_1,alpha'',A''_2) -> 0)$
  лежит в $Ex (italic("co")(F))$, то
  $ [A_1,alpha,A_2]_F=[A'_1,alpha',A'_2]_F+[A''_1,alpha'',A''_2]_F; $
] <ax:relative-exact-k0-additivity>
#named-axiom[
  Если $(A,alpha,B),(B,beta,C) in italic("co")(F)$, то
  $ [A,beta alpha,C]_F=[A,alpha,B]_F+[B,beta,C]_F $
] <ax:relative-exact-k0-composition>
(см. @prop:relative-grothendieck-composition-presentation). Из этих определений
следует существование канонических эпиморфизмов
$K_i (bold(C),plus.o) -> K_i (bold(C))$ ($i=0,1$) и
$K'_0 (F,plus.o) -> K'_0 (F)$. Кроме того, функтор $F$ индуцирует гомоморфизмы
$K_i (bold(C)) -> K_i (bold(C)')$ ($i=0,1$), при которых соответственно
$[A]_(bold(C)) |-> [F A]_(bold(C)')$ и
$[A,alpha]_(bold(C)) |-> [F A,F alpha]_(bold(C)')$. Можно рассмотреть
коммутативный квадрат
$ #exact-quotient-square() $
где $d[A,alpha,B]_F=[A]_(bold(C))-[B]_(bold(C))$, а отображение $d_(plus.o)$
определено аналогично.
