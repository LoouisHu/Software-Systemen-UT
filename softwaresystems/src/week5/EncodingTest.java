package week5;

import org.apache.commons.codec.DecoderException;
import org.apache.commons.codec.binary.Base64;
import org.apache.commons.codec.binary.Hex;

/**
 * A simple class that experiments with the Hex encoding
 * of the Apache Commons Codec library.
 *
 */
public class EncodingTest {
    public static void main(String[] args) throws DecoderException {
        String input = "Hello World";
        String input2 = "010203040506";
        String input3 = "U29mdHdhcmUgU31zdGVtcw==";
        String input4 = "a";
        String input5 = "aa";
        String input6 = "aaa";
        String input7 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        System.out.println("Hex from Hello World = " + Hex.encodeHexString(input.getBytes()));
        System.out.println("Encoded Base64 of Hello World = " + Base64.encodeBase64String(input.getBytes()));
        System.out.println(Base64.encodeBase64String(Hex.decodeHex(input2.toCharArray())));
        System.out.println(Base64.isBase64(input3.toString()));
        System.out.println(Base64.encodeBase64String(input4.getBytes()));
        System.out.println(Base64.encodeBase64String(input5.getBytes()));
        System.out.println(Base64.encodeBase64String(input6.getBytes()));
        System.out.println(Base64.encodeBase64String(input7.getBytes()));
    }

}
