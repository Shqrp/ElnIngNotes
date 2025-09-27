#import "@preview/theorion:0.3.3": *
#import "@preview/cetz:0.3.4"
#import "@preview/cetz-plot:0.1.1"
#import math: *

#import cosmos.rainbow: *

#show: show-theorion

#set text(lang: "it")
#set page(numbering: "I", footer: [], header: context {
  if counter(page).display() != "I" {
    if calc.even(counter(page).get().at(0)) {
      align(left, [#{ counter(page).display() } - _Analisi Matematica I_])
    } else {
      align(right, [_Analisi Matematica I_ - #{ counter(page).display() }])
    }
  }
})

#align(center, heading(outlined: false, [Analisi Matematica I]))
#align(
  center,
  [Andrea Giurgola - Prof. Fabio Punzo \ Ingegneria Elettronica, Politecnico di Milano],
) \

#set heading(numbering: "1.1.")
#set-theorion-numbering("1.1")
#outline(title: [Indice])

#pagebreak()
#counter(page).update(1)
#set page(numbering: "1")
= Richiamo di logica

La logica si basa su *predicati* (o *affermazioni*), i quali possono essere veri o falsi e si connettono tra loro tramite connettivi:
- *Implicazione logica* ($=>$): se l'antecedente è vero allora anche il conseguente sarà vero, ma non vale il contrario
- *Equivalenza logica* ($<=>$): la verità di uno dei due predicati implica la verità dell'altro e viceversa
- *Contrapposizione*: data un'implicazione ($p => q$) allora sarà anche vero l'implicazione di senso inverso degli opposti dei due predicati (se $p => q$, allora anche $overline(q) => overline(p)$)

Alla base della matematica esiste il *teorema*, ossia un'implicazione logica in cui l'antecedente si dice *ipotesi* e il conseguente si dice *tesi*. La *dimostrazione* è una catena di passaggi logici che giustifica tale implicazione. Esistono tre tipi di dimostrazioni:
- *Diretta*: viene dimostrato che l'ipotesi implica la tesi
- *Indiretta per contrapposizione*: viene dimostrato che l'inverso della tesi implica l'inverso dell'ipotesi
- *Indiretta per assurdo*: viene dimostrato che la negazione della tesi porta ad un risultato falso, rendendo dunque vera la tesi
- *Per induzione*: un tipo di dimostrazione che vale solo all'interno dei numeri naturali

Esistono tre quattro diverse tipologie di teorema:
- *Lemma*: un teorema di piccola importanza
- *Proposizione*: un teorema di media importanza
- *Teorema*
- *Corollario*: l'insieme di conseguenze di un teorema

== Il principio di induzione

Il *principio di induzione* è un principio dimostrativo che permette di dimostrare un teorema in $NN$ riducendo notevolmente il numero di passaggi necessari. \
Sia $p(n)$ una proposizione logica che dipende dalla variabile $n in NN$. Se $p(n)$ è valida per $n = 0$ (*ipotesi* o *base induttiva*), allora sarà vera anche per $n = 0 + 1$ (*passo induttivo*), e così via. Secondo il principio di induzione, allora $p(n)$ è vera $forall n in NN$. Di seguito tre esempi di teoremi dimostrabili con il principio di induzione.

#theorem(
  title: [Somma dei primi $n$-naturali],
  
  [$ sum^n_(k=1)k = n/2(n+1), forall n in NN $
],
)
#proof([
  Sia $p(n)$ la suddetta relazione. \
  $p(0)$: $0 = 0/2(0+1), 0 = 0$. Pertanto $p(0)$ è vera. \
  $p(n + 1)$: $1 + 2 + 3 + ... + n + (n + 1) = (n + 1)/2[(n + 1) + 1]$ \
  Riscrivendo la somma fino a $n$ come $p(n)$ \
  $(1 + 2 + 3 + ... + n) + (n + 1) = n/2(n + 1) + (n + 1) = (n + 1)(n/2 + 1) = (n + 1)((n + 2)/2) = (n + 1)/2(n + 1 + 1)$. \ In quanto si è ritornati alla scrittura di $p(n + 1)$, allora è verificato che $p(n) => p(n + 1)$, dunque, per il principio di induzione, il teorema vale $forall n in NN$.
]) \ \

#theorem(title: [Disuguaglianza di Bernoulli], [
  Sia $h in RR, h > -1$. Pertanto $(1+h)^n >= 1 + n h, forall n in NN$.
])
#proof([
  Sia $p(n)$ la suddetta disuguaglianza. \
  $p(0)$: $(1 + h)^0 >= 1 + 0, 1 >= 1$. Pertanto $p(0)$ è verificata.\
  $p(n + 1)$: $(1 + h)^(n + 1) >= 1 + (n + 1)h$ \
  $(1 + h)^(n + 1) = (1 + h)^n (1 + h)$. Si nota che $1 + h > 0$ e che $(1 + h)^n >= (1 + n h)$. Dunque \
  $(1 + h)^n (1 + h) >= (1 + n h)(1 + h) = n h^2 + n h + h + 1$. Dunque \
  $(1 + h)^(n + 1) >= n h^2 + n h + h + 1$. $n h^2$ si può non considerare in quanto rende solo più forte la relazione di disuguaglianza. Dunque \
  $(1 + h)^(n + 1) >= n h + h + 1, (1 + h)^(n + 1) >= 1 + (n + 1)h$. \
  È verificato che $p(n) => p(n + 1)$, dunque, per il principio di induzione, $p(n)$ è vera $forall n in NN$.
])

#proposition(
  title: [Somma della progressione geometrica],
  [
    Sia $q in RR, q != 1$. $sum^n_(k = 0)q^k = (1 - q^(n + 1))/(1 - q), forall n in NN$
  ],
)
#proof([
  #set par(leading: 1.065em)
  Sia $p(n)$ la suddetta proposizione. \
  $p(0)$: $q^0 = (1 - q^1)/(1 - q), 1 = cancel(1 - q)/cancel(1 - q), 1 = 1$. Pertanto $p(0)$ è vera. \
  $p(n + 1)$: $sum^(n + 1)_(k = 0)q^k = (1 - q^(n + 2))/(1 - q), sum^(n + 1)_(k = 0)q^k = sum^(n)_(k = 0)q^k + q^(n + 1) = (1 - q^(n + 1))/(1 - q) + q^(n + 1) =$ \
  $= (1 - cancel(q^(n + 1)) + cancel(q^(n + 1)) - q^(n + 2))/(1 - q) = (1 - q^(n + 2))/(1 - q)$. \ È verificato che $p(n) => p(n + 1)$, dunque, per il principio di induzione, $p(n)$ è vera $forall n in NN$.
])

= I numeri

Tra gli insiemi numerici di base si possono annoverare i seguenti:
- *Numeri naturali*: comprende tutti i numeri interi positivi maggiori o uguali a 0
$ NN := {0,1,2,3,...} $
- *Numeri interi relativi*: comprende tutti i numeri interi positivi e negativi
$ ZZ := {..., -2, -1, 0, 1, 2, ...} $
- *Numeri razionali*: comprende tutti i numeri esprimibili come rapporto tra due interi
$ QQ := { m/n : m,n in italic(ZZ), n != 0 } $

Quindi, in sintesi, $NN subset ZZ subset QQ$. \ \

== I numeri razionali

Due frazioni $a/b$ e $c/d$ si dicono *equivalenti* se vale la relazione $a d = b c$. \

I numeri razionali possono anche essere rappresentati sotto forma di *allineamento decimale* (per esempio $1/2 = 0,5$). Un numero razionale può essere:
- *finito*: la parte decimale ha un numero limitato di cifre
- *periodico*: la parte decimale si ripete all'infinito con costanza

#note-box([Gli allineamenti decimali con periodo $9$ non provengono da alcuna divisione (ad esempio $0.overline(9) = 1$).])

#definition([
  Sia $n in ZZ$. $n$ si dice:
  - _pari_: $exists h in ZZ : n = 2h$
  - _dispari_: $exists h in ZZ : n = 2h + 1$
]) <raz:defpari>
#proposition(
  title: [Parità dei quadrati],
  [$n$ pari $=> n^2$ pari, $n$ dispari $=> n^2$ dispari],
) <raz:pdq>
#proof([\ Sia $n in ZZ$. $n$ è pari $<=> exists h in ZZ : n = 2h$. Dunque \
  $n^2 = (2h)^2 = 4h^2 = 2(2h^2) = 2k$, essendo $k = 2h^2 in ZZ$. \
  Dunque $n^2$ è pari \ \
  Sia $n in ZZ$. $n$ è dispari $<=> exists h in ZZ : n = 2h + 1$. Dunque \
  $n^2 = (2h +1)^2 = 4h^2 + 4h + 1 = 2(2h^2 +2h) + 1 = 2k + 1$ dove $k = 2h^2 + 2h$. \
  Dunque $n^2$ è dispari
])
#proposition(
  title: [Parità dei quadrati inversa],
  [$n^2$ pari $=> n$ pari, $n^2$ dispari $=> n$ dispari],
) <raz:pdq2>
#proof([Sia $n in ZZ$. Introducendo i predicati $cal(P)$: $n$ è dispari e $cal(Q)$: $n^2$ è dispari, dalla @raz:pdq si inferisce che $cal(P) => cal(Q)$. Poiché la negazione di dispari è pari, allora, per contrapposizione, è vero che $overline(cal(Q)) => overline(cal(P))$. ])

=== Il problema delle radici

I numeri razionali presentano lacune in materia di estrazione di radici.
#definition([Sia $a >= 0$. Si dice _radice quadrata_ di $a$ un numero $b$ tale che $b^2 = a, b >= 0$.])
#theorem(
  title: [Irrazionalità di $sqrt(2)$],
  [$sqrt(2)$ non è un numero razionale.],
)
#proof([
  Supponiamo, per assurdo, che $sqrt(2) in QQ$. Dunque \
  $sqrt(2) = m/n$ essendo $m,n in ZZ, n != 0, m, n$ primi tra loro. Elevando al quadrato: \
  $2 = m^2/n^2 => m^2 = 2n^2$. Pertanto $m^2$ è pari e anche $m$ è pari. Dunque $exists k in Z : m = 2k$ \
  $2n^2 = m^2 = (2k)^2 = 4k^2 => 2n^2 = 4k^2 => n^2 = 2k^2$. Pertanto $n^2$ è pari, quindi anche $n$ è pari. \
  Questo è un assurdo, dal momento che $m$ e $n$ sono per definizione primi tra loro, quindi non possono essere entrambi pari.
]) \ \

== I numeri reali

L'insieme dei numeri reali rappresenta quell'insieme numerico che comprende *tutti gli allineamenti decimali finiti*,* infiniti periodici* e *infiniti non periodici*. Dunque:
$ NN subset ZZ subset QQ subset RR $

Tutti quei numeri reali che non sono razionali si dicono *numeri irrazionali*, i quali appartengono all'insieme $RR backslash QQ$.

=== La rappresentazione geometria di $RR$

Se si rappresentano i numeri razionali sulla retta, ci saranno sempre dei buchi (per es. ($sqrt(2) in RR$ ma $in.not QQ$). Invece i numeri reali, in quanto comprendono anche i non razionali, godono della *proprietà di continuità* (o *completezza*) *dei numeri reali*.
\
== Estremo superiore ed inferiore
Sia $E subset.eq RR$.
#definition([
  #set par(leading: 1.06em)
  - $M in RR$ si dice _massimo_ ($max E$) di E se $cases(M in E, M >= x\, forall x in E)$ \
  - $m in RR$ si dice _minimo_ ($min E$) di E se $cases(m in E, m <= x\,forall x in E)$
])
#example([$E = (0; 2] => max E = 2, exists.not min E$, $E = [0; 2) => exists.not max E, min E = 0$])
#definition([
  - $Lambda in RR$ si dice _maggiorante_ di E se $Lambda >= x, forall x in E$ \
  - $lambda in RR$ si dice _minorante_ di E se $lambda <= x, forall x in E$
])
#definition([Sia $E != emptyset$.
  - Si dice _estremo superiore_ ($sup E$) di E il minimo dei maggioranti
  - Si dice _estremo inferiore_ ($inf E$) di E il massimo dei minoranti.
])
#example($E = (0; 2] => sup E = 2 = max E, inf E = 0$)
#note-box([Se $exists max E$ allora coincide con $sup E$.])

L'estremo superiore è caratterizzato da due proprietà:
- $sup E$ è un maggiorante di E: $sup E >= x, forall x in E$
- Qualunque numero $< sup E$ non è un maggiorante di E: $forall epsilon > 0 #" " exists x_epsilon in E : x_epsilon > sup E - epsilon$
L'estremo inferiore di E è caratterizzato da:
- $inf E$ è minorante di E: $inf E <= x, forall x in E$
- Qualunque numero $> inf E$ non è minorante di E: $forall epsilon > 0 #" " exists x_epsilon in E : x_epsilon < inf E + epsilon$
\
#definition([
  + $E$ si dice _limitato superiormente_ se ammette almeno un maggiorante ($exists Lambda in RR, Lambda >= x, forall x in E$)
  + $E$ si dice _limitato inferiormente_ se ammette almeno un minorante ($exists lambda in RR, lambda <= x, forall x in E$)
  + $E$ si dice _limitato_ se lo è sia inferiormente che superiormente ($exists Lambda, lambda in RR : lambda <= x <= Lambda, forall x in E$)
])
#note-box([
  + $E$ non è limitato superiormente $<=> exists x in E : x >= Lambda, forall Lambda in RR => sup E = +infinity$
  + $E$ non è limitato inferiormente $<=> exists x in E : x <= lambda, forall lambda in RR => inf E = -infinity$
])
#theorem(
  title: [Proprietà di continuità/completezza di $RR$],
  [
    Un insieme $E subset.eq RR != emptyset$ limitato superiormente ha sempre un $sup E$ in $RR$. Analogamente, un insieme $E$ limitato inferiormente ha sempre un $inf E$ in $RR$.
  ],
) <esi:pcrr>
#corollary([
  Se $E subset.eq RR != emptyset$, allora $exists sup E, inf E in RR$
])
#example([
  Sia $A = { x in QQ : x^2 <= 2 } subset.eq QQ subset.eq RR => sup A = sqrt(2)$ \
  In questo caso l'estremo superiore appartiene a $RR$ ma non a $QQ$, dunque osserviamo che in $QQ$ la proprietà di completezza è falsa. \
])

== Potenze e radici

Grazie alla proprietà di continuità di $RR$ vale il seguente teorema.
#theorem(
  title: [Radice $n$-esima di un numero],
  [
    Sia $n in NN, y in RR : n >= 1, y > 0$. Allora $exists x in RR : x^n = y$, dove $x$ si dice la _radice $n$-esima_ di $y$.
  ],
)

Siano $r = m/n, a > 0$, con $m in ZZ, n in NN, n != 0$. Allora si può dire che
$ a^r := (a^m)^(1/n) = root(n, a^m) $
Inoltre, se $n$ è dispari, vale anche la seguente relazione.
$ (-a)^r = -root(n, a^m) $
Ora siano $a > 0, b in RR$. $a^b$ rappresenta una *potenza ad esponente reale*. Dunque
$
  a > 1 <=> a^b := sup {a^r : r in QQ, r <= b} \
  a < 1 <=> a^b := sup {a^r : r in QQ, r >= b}
$
In altre parole, se consideriamo la potenza $a^b$ per un qualsiasi numero reale $b$, essa rappresenta l'estremo superiore dell'insieme delle potenze di $a$. Nel caso $a > 1$, gli esponenti delle potenze nell'insieme sono tutti minori o uguali di $b$, mentre nel caso $a < 1$, essi sono tutti maggiori di $b$.

#theorem(
  title: [Logaritmo di un numero in base $a$],
  [
    Siano $a > 0, a != 1, y > 0$. Allora $exists x in RR : a^x = y$ dove $x$ è detto il _logaritmo di $y$ in base $a$_.
  ],
)

== Valore assoluto

#definition(
  title: [Valore assoluto],
  [
    Si dice _valore assoluto_ o _modulo_ di un numero $x in RR$ \
    $ abs(x) := cases(x"   se" x >= 0, -x" se" x < 0) $
  ],
)
#warning-box([Sia $a in RR$. Allora $sqrt(a^2) = abs(a)$ poiché il risultato di una radice di ordine pari è sempre positivo.])

In altre parole, $abs(a) = max{a, -a} <=> abs(a) = abs(-a), a <= abs(a), -a <= abs(a)$.

#theorem(title: [Disuguaglianza triangolare], [
  $ abs(a + b) <= abs(a) + abs(b), forall a, b in RR $
]) 
#proof([Siano $a, b in RR$. \
  Sapendo che $a <= abs(a)$ e $b <= abs(b)$ e che $-a <= abs(a)$ e $-b <= abs(b)$ e sommando membro a membro si ha \
  $a + b <= abs(a) + abs(b), -a -b <= abs(a) + abs(b)$ \
  In virtù del fatto che $abs(a) = max{a, -a}$ allora $abs(a + b) = max{a + b, -a - b} <= abs(a) + abs(b)$.
])

Analogamente, è vera anche la relazione $abs(abs(a) - abs(b)) <= abs(a + b), forall a, b in RR$.

== I numeri complessi

#show math.Im: "Im"
#show math.Re: "Re"

Se consideriamo l'equazione $x^2 + 1 = 0$, sappiamo che non esistono soluzioni in $RR$. Per poterla risolvere dobbiamo introdurre l'*unità immaginaria* $i$, per la quale vale la seguente proprietà.
#definition(title: "Unità immaginaria", $ i^2 = -1 $)
Risulta dunque che la suddetta equazione ha come soluzione $x = plus.minus i$. \
Con questa unità è possibile costruire i cosiddetti *numeri complessi*, i quali assumono la forma di $z = a + b i, z in CC, a, b in RR$. $a$ corrisponde alla *parte reale* di $z$ ($a = Re z$) mentre $b$ alla *parte immaginaria* ($b = Im z$). \

I numeri complessi possono assumere tre forme diverse:
- *Forma algebrica*: $z = a + b i, forall a,b in RR$
- *Forma trigonometrica*: $z = r(cos theta + i sin theta), forall r in RR, forall theta in [0 + 2k pi, 2pi + 2k pi), forall k in NN$
- *Forma esponenziale*: $z = r e^(i theta), forall r in RR, forall theta in (0 + 2k pi, 2pi + 2k pi), forall k in NN$

=== Operazioni tra numeri complessi

La somma tra $z = a + b i, w = c + d i in CC$ si svolge utilizzando le normali regole dell'algebra. 
$ z + w = a + b i + c + d i = a + c + (b + d)i $
Analogamente, anche il prodotto si svolge allo stesso modo
$ z w = (a + b i)(c + d i) = a c + b c i + a d i + b d i^2 = a c - b d + (b c + a d)i $ \
L'*opposto* di un numero complesso è $-z = - a - b i$ mentre l'*inverso* non è così immediato. Infatti
$ z^(-1) = (a + b i)^(-1) = 1/(a + b i) = 1/(a + b i)(a - b i)/(a - b i) = (a - b i)/(a^2 + b^2) = a/(a^2 + b^2) - b/(a^2 + b^2)i $
Il quarto passaggio è necessario affinché si possa arrivare ad un forma che possa comunque ricondurre ad una parte reale ed una parte immaginaria distinte. \
Il *coniugato* di un numero complesso è lui stesso con la parte immaginaria invertita. Dunque
$ overline(z) = a - b i $
Il *modulo* di un numero complesso vale invece
$ abs(z) = sqrt(a^2 + b^2) $

Queste due formule ci permettono di riscrivere l'inverso e il prodotto tra $z$ e $overline(z)$ come
$ overline(z)z = abs(z)^2, z^(-1) = overline(z)/abs(z)^2 $
Risulta inoltre che il coniugato del prodotto $z w$ è uguale al prodotto dei coniugati ($overline(z w) = overline(z) dot overline(w)$)
Sappiamo anche che il modulo di $z$ ha le seguenti proprietà.
$ abs(z) >= 0, forall z in CC, abs(z) = 0 <=> z = 0 \
abs(Re z) <= abs(z), abs(Im z) <= abs(z) $
E il coniugato ha queste altre proprietà.
$ z + overline(z) = 2 Re z, z - overline(z) = 2 Im z $
Infine la divisione tra due numeri complessi $z, w in CC, w != 0$ avviene come il prodotto, dunque
$ z/w = z 1/w = z overline(w)/abs(w)^2 $
#example([
  $(1 - 2i)/(1 + i) = (1 - 2i) 1/(1 + i) = (1 - 2i) (1 - i)/(1 + 1) = (1 - 2i) (1 - i)/2 = 1/2 (1 - 2i - i - 2) = 1/2 (1 - 3i)$
])
#theorem(title: [Disuguaglianza triangolare in $CC$], [
  $ abs(z + w) <= abs(z) + abs(w), forall z, w in CC $
])

=== Piano di Argand-Gauss

Dato $z in CC, z = a + b i$ esso si può rappresentare nel cosiddetto *piano di Argand-Gauss* o, più comunemente, *piano di Gauss*. Basta far corrispondere all'ascissa la $Re z$ e all'ordinata la $Im z$.

// #cetz.canvas({
//   import cetz.draw: *
//   import cetz-plot: *
//   plot.plot(size: (4, 4), axis-style: "school-book", {
//     plot.add(())
//   })
// })

=== Forma trigonometrica di $z$

Dato $z = x + y i$, diciamo $theta$ l'angolo che si forma tra il segmento $z$ è l'asse $x$. Questo ci permette di individuare $z$ utilizzando solo $abs(z)$, ossia la distanza da $z$ all'origine, e $theta$, detto anche *argomento* di $z$. Per tornare alla forma algebrica, è necessario calcolare $x$ e $y$, i quali valgono:
$ x = abs(z)cos theta, y = abs(z)sin theta => z = abs(z)cos theta + i abs(z)sin theta = abs(z)(cos theta + i sin theta) $
Ogni coppia $(abs(z), theta)$ individua uno e uno solo $z$. \ \ \
Per convertire dalla forma algebrica alla forma trigonometrica, è necessario calcolare $abs(z)$ e $theta$. Notare che $theta$ è determinato a meno di multipli di $2 pi$, dunque è più appropriato considerare quel $theta in [0; 2pi)$ oppure in un qualsiasi intervallo semiaperto $[a, b)$ dove $b - a =2pi$. Perciò si parla di *argomento principale*. \

Per trovare $theta$ sappiamo che
$ y/x = (cancel(abs(z))sin theta)/(cancel(abs(z)) cos theta) = (sin theta)/(cos theta) = tan theta \ 
"se" x > 0 => theta = arctan(y/x), "se" x < 0 => theta = arctan(y/x) + pi $

Il prodotto con la forma trigonometrica segue le normali regole dell'algebra e della goniometria. Siano $z = r(cos theta + i sin theta), w = R(cos phi + i sin phi)$. Allora
$ z w &= r R(cos theta + i sin theta)(cos phi + i sin phi) = \
      &= r R(cos theta cos phi + i sin theta cos phi i cos theta sin phi + i^2 sin theta sin phi) = \
      &= r R(underbracket(cos theta cos phi - sin theta sin phi, cos (theta + phi)) + i(underbracket(cos theta sin phi + sin theta cos phi, sin (theta + phi)))) = \
      &= r R(cos (theta + phi) + i sin (theta + phi))
$

Dunque il prodotto tra due numeri complessi $z$ e $w$ presenta come modulo il prodotto dei moduli e come argomento la somma degli argomenti.
#note-box([In altre parole, moltiplicare $z$ per $w$ agisce come:
- _dilatazione_ o _compressione_ di $abs(z)$ (in base a se $abs(w) > 1$ o $abs(w) < 1$)
- _rotazione_ di $z$ di angolo $phi$])
Grazie a questa caratteristica, è possibile ottenere una formula analoga per le potenze.
#definition(title: [Formula di De Moivre], [
  Sia $z = r(cos theta + i sin theta), n in NN$. Allora $z^n = r^n (cos n theta + i sin n theta)$
])
Questa formula rende comoda l'elevazione a potenza di numeri complessi, che in forma algebrica sarebbe invece molto tediosa.

=== Forma esponenziale di $z$

La forma esponenziale di un numero complesso si fonda sull'*identità di Eulero*.
#definition(title: [Identità di Eulero], $ e^(i theta) = cos theta + i sin theta $)
Dunque, prendendo l'esempio precedente del prodotto tra $z$ e $w$ ma in forma esponenziale:
$ z w &= r e^(i theta) R e^(i phi) = r R e^(i theta + i phi) = r R e^i(theta + phi) \
z^n &= (r e^(i theta))^n = r^n e^(i n theta), forall n in NN $

=== Radici $n$-esime di $z$

#theorem(title: [Radici $n$-esime di $z$], [
  Sia $w in CC$. Le radici $n$-esime di $w$ sono tutti gli $n$ $z in CC$ tali che $z^n = w$.
])
#proof([Siano $w = R e^(i phi)$ e $z = r e^(i theta)$. Allora \
  $ z^n = r^n e^(n i theta) = R e^(i phi) => cases(r^n = R, n theta = phi + 2k pi\, k in ZZ) $
  Dunque $r = root(n, R)$ e $theta = (phi + 2k pi)/n$. Dividendo con resto $k$ per $n$, otterremo un resto $k = s n + h$, con $h = 0, 1, 2,...,n-1$. Pertanto \
  $ theta = (phi + 2(s n + h)pi)/n = (phi + 2h pi)/n + 2 s pi => 2s pi "è eliminabile perché multiplo di" 2 pi $ \
  Quindi prendiamo solo $theta = (phi + 2h pi)/n$ con $h = 0, 1, 2,..., n - 1$. Dunque abbiamo $n$ radici di $w$.
])

#theorem(title: [Teorema fondamentale dell'algebra], [
  Un'equazione polinomiale del tipo: $a_n z_n + a_(n-1) z_(n-1) + ... + a_0 z_0 = 0$ con $a_n, a_(n-1), ..., a_0 in CC$ e $a_n != 0$ ammette esattamente $n$ soluzioni appartenenti a $CC$ purché ciascuna sia contata con la propria molteplicità.
]) <cpl:fond>

==== Radici di 1

In $RR$, esiste solo una radice $n$-esima di 1, mentre in $CC$ ne esistono $n$ per il @cpl:fond. Se le rappresentiamo sul piano di Gauss, esse si trovano sulla circonferenza unitaria e costituiscono un poligono regolare di $n$ lati.

= Funzioni

Siano $A, B$ due insiemi. Una funzione $f: A -> B$ è una *legge* che associa ad ogni elemento di $A$ *uno e uno solo* di $B$. Si denota come $y = f(x)$. $A$ è detto *dominio*, mentre $B$ *codominio*.

#definition(title: [Immagine del dominio], [
  Si dice _immagine di $A$_ tramite $f$ l'insieme degli elementi di $B$ che provengono da qualche elemento di $A$. In simboli:
  $ Im(f) eq.triple f(A) := {y in B: exists x in A, y = f(x)} $
])

#definition(title: [Tipologie di funzioni], [
  Siano $A, B$ due insiemi, $f: A -> B$. $f$ si dice:
  - _iniettiva_: $forall x_1, x_2 in A, x_1 != x_2 => f(x_1) != f(x_2)$ oppure $f(x_1) = f(x_2) => x_1 = x_2$
  - _suriettiva_: $B = Im(f)$
  - _biiettiva_ (o _bigiettiva_ o _biunivoca_): $f$ è sia suriettiva che iniettiva
])
Dunque una funzione è iniettiva quando ad ogni $x$ corrisponde *una sola* $y$ ed è suriettiva quando ogni elemento del codominio è immagine di almeno un elemento del dominio. 

Se $f$ è iniettiva, allora è invertibile su $f(A)$ e non su tutto $B$. In altre parole, è ben definita la *funzione inversa* $f^(-1): f(A) -> A$. Se $f$ è biiettiva, allora è invertibile su tutto $B$. Infatti $f^(-1): B -> A$.

#definition(title: [Controimmagine], [
  Siano $f: A -> B, D subset.eq B$. Si dice _controimmagine_ (o _antiimmagine_) di D l'immagine della $f^(-1)$ con dominio $D$. In simboli:
  $ f^(-1)(D) := {x in A : f(x) in D} $
])
Un'operazione che si può svolgere tra funzioni è la *composizione*.
#definition(title: [Funzione composta], [
  Siano $f: A -> B, g: B -> C$. Allora $g compose f := g[f(x)]$ dove $g compose f: A -> C$.
])
Va notato che la composizione non è commutativa, dunque $g compose f != f compose g$.
#note-box([
  Se una funzione $f: A -> B$ è iniettiva, allora:
  - $(f^(-1) compose f)(x) = f^(-1)[f(x)] = x, forall x in A$
  - $(f^(-1) compose f)(y) = f^(-1)[f(y)] = y, forall y in B$
])
#definition(title: [Funzione reale di una variabile reale], [
  Siano $A subset.eq RR, B subset.eq RR, f: A -> B$. Allora $f$ si dice _funzione reale di una variabile reale_.
])

== Insieme di definizione

In molti casi, una funzione è data da un'espressione analitica (es. $f(x) = sqrt(x + 1)$, $f(x) = log(1 - x^2)$), dunque non definendo esplicitamente dominio e codominio. Pertanto si assume che il codominio sia $RR$ e che il dominio sia l'*insieme di definizione* di $f$, ossia l'insieme di tutte le $x in RR$ tali che le operazioni che compaiono nell'espressione di $f(x)$ hanno senso. \
#example([
  $f(x) = sqrt(x - 1), " " D = { x in RR : x - 1 >= 0} = {x in RR : x >= 1} = [1; +infinity)$
])

== Funzioni monotòne
#definition(title: [Funzione monotona], [
    Siano $A subset.eq RR, f: A -> RR$. $forall x_1, x_2 in A, x_1 < x_2$, $f$ si dice:
    - _crescente_: $f(x_1) <= f(x_2)$
    - _decrescente_: $f(x_1) >= f(x_2)$
    - _strettamente crescente_: $f(x_1) < f(x_2)$
    - _strettamente decrescente_: $f(x_1) > f(x_2)$
    Dunque $f$ si dice:
    - _monotona_ se è crescente o decrescente
    - _strettamente monotona_ se è strettamente crescente o strettamente decrescente
])
#note-box([
  Se il rapporto incrementale di $f$ ($(f(x_1) + f(x_2))/(x_1 - x_2), forall x_1, x_2 in A, x_1 != x_2$) è positivo, allora $f$ è crescente. Viceversa, $f$ è decrescente.
])

== Grafico di una funzione

#definition(title: [Grafico di $f$], [
  Sia $f:A -> B$. Allora $G_f := {(x, f(x)) : x in A}$ si dice _grafico di $f$_.
])
Se dominio e codominio di $f$ sono contenuti in $RR$, allora $G_f$ può essere rappresentato nel piano cartesiano $O x y$.

#pagebreak()
#outline(title: [Indice dei teoremi e dimostrazioni], target: figure.where(
  kind: "theorem",
))
