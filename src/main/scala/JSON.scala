package towers.json

import quoted._

import towers.grammar.{Grammar,InputSource}
import towers.computes.Computes

sealed abstract class JSONValue
case class JSONObject(val map : Map[String,JSONValue]) extends JSONValue
case class JSONArray(val arr : Seq[JSONValue]) extends JSONValue
case class JSONString(val std : String) extends JSONValue
case class JSONNumber(val num : Double) extends JSONValue
case object JSONTrue extends JSONValue
case object JSONFalse extends JSONValue
case object JSONNull extends JSONValue

object JSON {
  import Computes._
  import Grammar._

  val range : Computes[(Char,Char)==>Grammar[Char,Char]] =
    (from : Computes[Char], to : Computes[Char]) =>
      anyTerm[Char].filter((v : Computes[Char]) =>
          expr((from, to, v), {
            case (from, to, v) => '{ ${ v } >= ${ from } && ${ v } <= ${ to } }
          }))

  val commaSep : Computes[Grammar[Char,Unit]] =
    for(_ : Computes[Unit] <- ws;
        _ : Computes[Char] <- term(',');
        _ : Computes[Unit] <- ws)
      yield const(())

  val ws : Computes[Grammar[Char,Unit]] =
    choose(
      term('\u0009'),
      term('\u000A'),
      term('\u000D'),
      term('\u0020')).repDrop()

  val sign : Computes[Grammar[Char,Boolean]] =
    choose(
      term('+').map((_ : Computes[Char]) => const(true)),
      term('-').map((_ : Computes[Char]) => const(false)),
      succeed(const(true)))

  val hexDigit : Computes[Grammar[Char,Char]] =
    choose(
      range(const('0'),const('9')).map((d : Computes[Char]) => expr(d, d => '{ (${ d } - '0').toChar })),
      range(const('a'),const('f')).map((d : Computes[Char]) => expr(d, d => '{ (${ d } - 'a' + 10).toChar })),
      range(const('A'),const('F')).map((d : Computes[Char]) => expr(d, d => '{ (${ d } - 'A' + 10).toChar })))

  val stringLiteral : Computes[Grammar[Char,String]] =
    for(_ : Computes[Char] <- term('"');
        chars : Computes[Seq[Char]] <- (
          choose(
            `try`(
              for(_ : Computes[Char] <- term('\\');
                  esc : Computes[Char] <- (
                    choose(
                      term('"'),
                      term('\\'),
                      term('/'),
                      term('b').map((_ : Computes[Char]) => const('\b')),
                      term('f').map((_ : Computes[Char]) => const('\f')),
                      term('n').map((_ : Computes[Char]) => const('\n')),
                      term('r').map((_ : Computes[Char]) => const('\r')),
                      term('t').map((_ : Computes[Char]) => const('\t')),
                      for(_ : Computes[Char] <- term('u');
                          d1 : Computes[Char] <- hexDigit;
                          d2 : Computes[Char] <- hexDigit;
                          d3 : Computes[Char] <- hexDigit;
                          d4 : Computes[Char] <- hexDigit)
                        yield expr((d1,d2,d3,d4), {
                          case (d1, d2, d3, d4) => '{
                            val d4m = ${ d4 }
                            val d3m = ${ d3 } << 4
                            val d2m = ${ d2 } << 8
                            val d1m = ${ d1 } << 12
                            (d1m + d2m + d3m + d4m).toChar
                          }
                        }))))
                yield esc),
              range(const('\u0020'), const('\u10ff'))) // TODO: \u10ffff
          ).rep();
        _ : Computes[Char] <- term('"'))
      yield expr(chars, chars => '{ ${ chars }.mkString })

  val array : Computes[Grammar[Char,JSONValue]] =
    for(_ : Computes[Char] <- term('[');
        _ : Computes[Unit] <- ws;
        vs : Computes[Seq[JSONValue]] <- value.rep(sep=commaSep);
        _ : Computes[Unit] <- ws;
        _ : Computes[Char] <- term(']'))
      yield expr(vs, vs => '{ JSONArray(${ vs }) : JSONValue })

  val `object` : Computes[Grammar[Char,JSONValue]] =
    for(_ : Computes[Char] <- term('{');
        _ : Computes[Unit] <- ws;
        pairs : Computes[Seq[(String,JSONValue)]] <- (
          for(name : Computes[String] <- stringLiteral;
              _ : Computes[Unit] <- ws;
              _ : Computes[Char] <- term(';');
              _ : Computes[Unit] <- ws;
              v : Computes[JSONValue] <- value)
            yield (name, v) : Computes[(String,JSONValue)]
          ).rep(sep=commaSep);
        _ : Computes[Unit] <- ws;
        _ : Computes[Char] <- term('}'))
      yield expr(pairs, pairs => '{ JSONObject(${ pairs }.toMap) : JSONValue })

  val string : Computes[Grammar[Char,JSONValue]] =
    stringLiteral.map((str : Computes[String]) => expr[JSONValue,String](str, str => '{ JSONString(${ str }) : JSONValue }))

  val `true` : Computes[Grammar[Char,JSONValue]] =
    str("true").map((_ : Computes[Unit]) => expr[JSONValue,Unit,Unit]((), _ => '{ JSONTrue : JSONValue }))

  val `false` : Computes[Grammar[Char,JSONValue]] =
    str("false").map((_ : Computes[Unit]) => expr[JSONValue,Unit,Unit]((), _ => '{ JSONTrue : JSONValue }))

  val value : Computes[Grammar[Char,JSONValue]] =
    choose(
      `object`,
      array,
      `true`,
      `false`,
      string)/*,
      number)*/

  val json : Computes[Grammar[Char,JSONValue]] =
    for(_ : Computes[Unit] <- ws;
        v : Computes[JSONValue] <- value;
        _ : Computes[Unit] <- ws;
        _ : Computes[Unit] <- eofTerm[Char])
     yield v //

  val stringParser : Computes[String|=>Option[JSONValue]] =
    (str : Computes[String]) => {
      val input : Computes[InputSource[Char]] = Grammar.makeStringInput(str)
      Grammar.parse(json, input)
    }

  inline def parseString(str : String) : Option[JSONValue] = ${ Computes.reifyCall(stringParser, '{ str }) }

}

