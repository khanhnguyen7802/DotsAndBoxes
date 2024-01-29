package utils;

import java.util.Scanner;
import protocol.Protocol;

/**
 * This is the Helper class, which has additional self-written functions
 * to facilitate the flow of program.
 */
public class Helper {
    /**
     * Given an index, this method puts a replaced string
     * into an original string starting from that index.
     *
     * Example: motorbike -> myReplace("motorbike", "ship", 0) turns to "shiprbike")
     * @param origin the original String
     * @param replacement the replaced string
     * @param start starting index in the original string
     * @return
     */



    public static String myReplace(String origin, String replacement, int start) {



        char[] originCharArray = origin.toCharArray();
        char[] replacedCharArray = replacement.toCharArray();

        for (int i = 0; i < replacedCharArray.length; i++) {
            originCharArray[start] = replacedCharArray[i];
            start++;
        }

        return new String(originCharArray);
    }
}
