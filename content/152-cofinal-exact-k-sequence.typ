#import "main-defs.typ": Aut, E, End, Ex, GL, K, idx, source
#import "statements.typ": (
  condition-item, condition-list, proof, proposition, theorem,
)
#import "diagrams/abelian-k-theory-exact.typ": cofinal-exact-comparison

== $K$-последовательность для кофинального точного функтора
<sec:cofinal-exact-k-sequence>

Пусть функтор $F: bold(C) -> bold(C)'$ допустим, где $bold(C)$ и $bold(C)'$ —
допустимые подкатегории абелевых категорий. Будем называть функтор $F$
_кофинальным_,#idx("кофинальный функтор")#idx("функтор кофинальный") если он
кофинален относительно $plus.o$ в смысле гл.~@ch:exact-k-sequences. Напомним,
что это означает возможность для $A' in bold(C)'$ найти объекты $A in bold(C)$ и
$B' in bold(C)'$, для которых $A' plus.o B' tilde.eq F A$. Аналогично если
функтор $F$ точный, то имеет смысл говорить о кофинальности функтора
$Ex (F): Ex (bold(C)) -> Ex (bold(C)')$. Последнее условие, очевидно, влечет
кофинальность самого функтора $F$ (обратное верно, если категория $bold(C)'$
полупроста).

Допустим теперь, что функтор $F$ _кофинален и точен_. Тогда имеет место
коммутативная диаграмма (из которой выброшено отображение $partial$):
$ #cofinal-exact-comparison() $ <eq:cofinal-exact-k-comparison>
в которой верхняя строка получается из последовательности, рассмотренной в
@th:cofinal-functor-exact-sequence. Отображения
$K_i (bold(C)) -> K_i (bold(C)')$ инду#source(312)цированы функтором $F$, а
отображение $d$ построено в конце §~@sec:abelian-grothendieck-whitehead.
Существование отображения $partial$, очевидно, эквивалентно следующему условию:
если
$(0 -> (A',alpha') -> (A,alpha) -> (A'',alpha'') -> 0) in Ex (Sigma bold(C)')$,
то $f partial[A,alpha]_(bold(C)',plus.o)
=f partial([A',alpha']_(bold(C)',plus.o)+[A'',alpha'']_(bold(C)',plus.o))$.

#proposition[
  Пусть, как и выше, функтор $F: bold(C) -> bold(C)'$ точный и кофинальный. Если
  функтор $Ex (F)$ кофинальный, то существует отображение
  $partial: K_1 (bold(C)') -> K'_0 (F)$, превращающее диаграмму
  @eq:cofinal-exact-k-comparison в коммутативную. Если функтор $Ex (F)$
  осуществляет сюръективное отображение на классы стабильно изоморфных объектов,
  то последовательность
  $ K'_0 (F) -> K_0 (bold(C)) -> K_0 (bold(C)') -> 0 $
  точна.
] <prop:cofinal-exact-boundary-descent>

Предположение о сюръективности означает, что если $A in Ex (bold(C)')$, то
существуют объекты $B,C in Ex (bold(C))$, для которых
$F C tilde.eq A plus.o F B$.

#proof[
  Чтобы убедиться в существовании отображения $partial$, надо для данной точной
  последовательности
  $ (A,alpha)=(0 -> (A_2,alpha_2) -> (A_1,alpha_1) -> (A_0,alpha_0) -> 0) $
  в категории $Sigma bold(C)'$ показать, что
  $f partial[A_1,alpha_1]_(bold(C)',plus.o)
  =f partial([A_0,alpha_0]_(bold(C)',plus.o)+[A_2,alpha_2]_(bold(C)',plus.o))$.
  В силу предположения функтор $Ex (F)$ кофинален и, следовательно,
  $A plus.o B tilde.eq F C$ для некоторых точных последовательностей
  $B in Ex (bold(C)')$ и $C in Ex (bold(C))$. Используя этот изоморфизм,
  получаем изоморфизм вида $(A plus.o B,alpha plus.o 1_B) tilde.eq (F C,gamma)$
  в категории $Sigma bold(C)'$ для некоторого $gamma$. Так как
  $[A_i,alpha_i]_(bold(C)',plus.o)
  =[A_i plus.o B_i,alpha_i plus.o 1_(B_i)]_(bold(C)',plus.o)$ ($0 <= i <= 2$),
  то достаточно установить нужное равенство для $(F C,gamma)$ (вместо
  $(A,alpha)$). Но $(C,gamma,C)$ — точная последовательность в
  $italic("co")(F)$. Используя аксиому @ax:relative-exact-k0-additivity из
  определения группы $K'_0 (F)$, получаем, что
  $
    f partial[F C_1,gamma_1]_(bold(C)',plus.o)
    =f[C_1,gamma_1,C_1]_(F,plus.o)
    =[C_1,gamma_1,C_1]_F
    =[C_0,gamma_0,C_0]_F+[C_2,gamma_2,C_2]_F
    =f partial(
      [F C_0,gamma_0]_(bold(C)',plus.o)+[F
        C_2,gamma_2]_(bold(C)',plus.o)
    ).
  $
  Доказав существование отображения $partial$, расширим диаграмму
  @eq:cofinal-exact-k-comparison до диаграммы
  $
    #cofinal-exact-comparison(kernels: true)
  $ <eq:cofinal-exact-k-kernel-complex>
  #source(313)где верхняя строка является ядром эпиморфизма из средней строки на
  нижнюю. Рассмотрим эту диаграмму как короткую точную последовательность
  комплексов (строк), в которых все невыписанные члены нулевые.

  Очевидно, что группа $N_5$ порождается элементами вида
  $chevron.l A chevron.r_(bold(C)')=[A_1]_(bold(C)',plus.o)
  -[A_0]_(bold(C)',plus.o)-[A_2]_(bold(C)',plus.o)$, где
  $A=(0 -> A_2 -> A_1 -> A_0 -> 0) in Ex (bold(C)')$. Если функтор $Ex (F)$
  осуществляет сюръективное отображение на классы стабильно изоморфных объектов,
  то $A plus.o F B tilde.eq F C$ для некоторых $B,C in Ex (bold(C))$, и поэтому
  $chevron.l A chevron.r_(bold(C)')=F(chevron.l C chevron.r_(bold(C))
    -chevron.l B chevron.r_(bold(C)))$, а тогда отображение $N_4 -> N_5$
  сюръективно. Кроме того, функтор $F$ также осуществляет сюръективное
  отображение на классы стабильно изоморфных объектов (если функтор $Ex (F)$
  обладает этим свойством), и, следовательно, отображение
  $K_0 (bold(C),plus.o) -> K_0 (bold(C)',plus.o)$ сюръективно. Средняя строка
  диаграммы @eq:cofinal-exact-k-kernel-complex ациклична в трех средних позициях
  (в силу @th:cofinal-functor-exact-sequence). Таким образом, из рассмотрения
  длинной гомологической последовательности для
  @eq:cofinal-exact-k-kernel-complex вытекает, что, как и утверждалось,
  последовательность $K'_0 (F) -> K_0 (bold(C)) -> K_0 (bold(C)') -> 0$ точна.
  Это завершает доказательство предложения @prop:cofinal-exact-boundary-descent.
]

#theorem[
  Пусть функтор $F: bold(C) -> bold(C)'$ точен и допустим (здесь $bold(C)$ и
  $bold(C)'$ — допустимые подкатегории абелевых категорий). Предположим, что
  функтор $Ex (F): Ex (bold(C)) -> Ex (bold(C)')$ кофинален. Тогда:
  #condition-list[
    #condition-item(format: "cyrillic")[если категория $bold(C)$ полупроста, то
      категория $bold(C)'$ также полупроста и все вертикальные отображения в
      рассмотренной выше диаграмме @eq:cofinal-exact-k-comparison являются
      изоморфизмами; в частности, последовательность
      $
        K_1 (bold(C)) -> K_1 (bold(C)') arrow.r^partial K'_0 (F) -> K_0
        (bold(C)) -> K_0 (bold(C)')
      $
      точна;] <cond:semisimple-exact-k-full-sequence>
    #condition-item(format: "cyrillic")[если категория $bold(C)'$ полупроста, то
      последовательность
      $
        K_1 (bold(C)') arrow.r^partial K'_0 (F) -> K_0 (bold(C)) -> K_0
        (bold(C)')
      $
      точна.] <cond:semisimple-target-exact-k-sequence>
  ]
] <th:semisimple-exact-k-sequence>

#proof[
  @cond:semisimple-exact-k-full-sequence Если $A in Ex (bold(C)')$, то найдутся
  объекты $B in Ex (bold(C)')$ и $C in Ex (bold(C))$, для которых
  $A plus.o B tilde.eq F C$. Так как в силу предположения последовательность $C$
  расщепляется, то расщепляется и последовательность $F C$, а следовательно, и
  последовательность $A$. Таким образом, категория $bold(C)'$ также полупроста.

  Очевидно, что при $i=0$ отображение $K_i (bold(C),plus.o) -> K_i (bold(C))$
  является изоморфизмом. Если $i=1$, то надо показать, что для
  $(A,alpha)=(0 -> (A_2,alpha_2) -> (A_1,alpha_1) -> (A_0,alpha_0) -> 0)
  in Ex (Sigma bold(C))$ справедливо равенство в группе $K_1 (bold(C),plus.o)$
  $ [alpha_1]=[alpha_2]+[alpha_0]. $
  #source(314)Так как категория $bold(C)$ полупроста, то последовательность $A$
  расщепляется и, следовательно, можно отождествить $A_1=A_2 plus.o A_0$. Тогда
  запишем $alpha_1$ в матричном виде относительно этого разложения:
  $
    alpha_1=mat(alpha_2, *; 0, alpha_0)
    =mat(alpha_2, 0; 0, alpha_0) mat(1_(A_2), *'; 0, 1_(A_0)),
  $
  и, следовательно, $alpha_1=(alpha_2 plus.o alpha_0)epsilon$, где $epsilon$
  соответствует правому множителю. В группе $K_1 (bold(C),plus.o)$ справедливо
  равенство
  $
    [alpha_1]=[alpha_2 plus.o alpha_0]+[epsilon]=[alpha_2]+[alpha_0]+[epsilon].
  $
  Осталось показать, что $[epsilon]=0$. Положим
  $
    epsilon'=epsilon plus.o 1_(A_1) in Aut_(bold(C)) (A_1 plus.o A_1)
    tilde.eq GL_2 (R), quad R=End_(bold(C)) (A_1).
  $
  Если поменять два прямых слагаемых $A_2$ модуля $A_1=A_2 plus.o A_0$ в модуле
  $A_1 plus.o A_1$, то мы убедимся, что $epsilon'$ соответствует элементу группы
  $GL_2 (R)$, сопряженному с матрицей вида $mat(1, e; 0, 1)$. Переходя к
  элементу $epsilon plus.o 1_(A_1) plus.o 1_(A_1)$ и группе $GL_3 (R)$
  соответственно, получаем, что рассмотренные выше элементарные матрицы попадают
  в $E_3 (R) subset [GL_3 (R),GL_3 (R)]$, т. е. в коммутант группы $GL_3 (R)$
  (см. @prop:whitehead-lemma). Таким образом, как и утверждалось,
  $[epsilon]=[epsilon plus.o 1_(A_1) plus.o 1_(A_1)]=0$.

  Желая убедиться в том, что отображение $K'_0 (F,plus.o) -> K'_0 (F)$ является
  изоморфизмом, надо показать, что если
  $
    (A,alpha,B)=(0 -> (A_2,alpha_2,B_2) -> (A_1,alpha_1,B_1) ->
      (A_0,alpha_0,B_0) -> 0)
    in Ex (italic("co")(F)),
  $
  то $[alpha_1]=[alpha_2]+[alpha_0]$ в группе $K'_0 (F,plus.o)$. Как и выше,
  поскольку последовательности $A$ и $B$ расщепляются, можно отождествить
  $A_1=A_2 plus.o A_0$, $B_1=B_2 plus.o B_0$ и получить матричное представление
  $
    alpha_1=mat(alpha_2, *; 0, alpha_0)
    =mat(alpha_2, 0; 0, alpha_0)mat(1_(F A_2), *'; 0, 1_(F A_0)).
  $
  В этом случае опять $alpha_1=(alpha_2 plus.o alpha_0)epsilon$, и нам надо
  показать, что $[epsilon]=0$ в группе $K'_0 (F,plus.o)$. Но
  $[epsilon]=partial[F(A_2 plus.o A_0),epsilon]_(bold(C)',plus.o)$. Так как
  категория $bold(C)'$ полупроста (это было доказано ранее), то по соображениям,
  аналогичным тем, которые были использованы в последнем абзаце, получаем, что
  $[F(A_2 plus.o A_0),epsilon]_(bold(C)',plus.o)=0$ в группе
  $K_1 (bold(C)',plus.o)$.

  Аналогично полупростота категории $bold(C)'$ влечет за собой тот факт, что
  отображение $K_i (bold(C)',plus.o) -> K_i (bold(C)')$ является изоморфизмом
  при $i=0,1$, и, следовательно, мы доказали, что все вертикальные отображения
  диаграммы @eq:cofinal-exact-k-comparison — изоморфизмы. Так как верхняя строка
  — точная последовательность (см. @th:cofinal-functor-exact-sequence), #source(
    315,
  )то точной является и нижняя строка. Это завершает доказательство части
  @cond:semisimple-exact-k-full-sequence.

  @cond:semisimple-target-exact-k-sequence Допустим сейчас, что лишь категория
  $bold(C)'$ полупроста. В силу части @cond:semisimple-exact-k-full-sequence
  доказательства диаграмма @eq:cofinal-exact-k-kernel-complex имеет вид
  $ #cofinal-exact-comparison(kernels: true, semisimple: true) $
  Будем рассматривать строки как комплексы. Через $H(X)$ обозначим группу
  гомологии на месте $X$ той строки, где встречается $X$. Тогда, рассматривая
  длинную гомологическую последовательность и учитывая точность средней строки в
  трех средних членах, убеждаемся в том, что и последовательность
  $ 0 -> H(K_1 (bold(C)')) -> N_3 -> N_4 -> H(K'_0 (F)) -> 0 $
  точна. Таким образом, утверждение @cond:semisimple-target-exact-k-sequence
  будет доказано, если мы покажем, что отображение $N_3 -> N_4$ сюръективно.
  Пусть
  $chevron.l A chevron.r_(bold(C))=[A_1]_(bold(C),plus.o)
  -[A_0]_(bold(C),plus.o)-[A_2]_(bold(C),plus.o)$
  — один из образующих группы $N_4$, где
  $A=(0 -> A_2 -> A_1 -> A_0 -> 0) in Ex (bold(C))$. Пусть
  $B=(0 -> A_2 -> A_2 plus.o A_0 -> A_0 -> 0)$ — расщепляющаяся
  последовательность. Так как функтор $F$ точный и категория $bold(C)'$
  полупростая, то последовательность $F A$ расщепляется. Поэтому существует
  изоморфизм вида
  $ alpha=(1_(F A_2),alpha_1,1_(F A_0)): F A -> F B. $
  Тогда $(A,alpha,B) in Ex (italic("co")(F))$, и, следовательно, этот объект
  определяет элемент $(A,alpha,B) in N_3$, для которого
  $d(A,alpha,B)=chevron.l A chevron.r_(bold(C))
  -chevron.l B chevron.r_(bold(C))$. Так как последовательность $B$
  расщепляется, то $chevron.l B chevron.r_(bold(C))=0$, что завершает
  доказательство.
]

Предположения о полупростоте в доказанной теореме весьма ограничительны. В
следующем параграфе будет дан «критерий редукции» для вычисления групп
$K_i (bold(C))$ исходя из подкатегории $bold(C)_0 subset bold(C)$. На практике
можно довольно часто найти такую полупростую подкатегорию $bold(C)_0$.
