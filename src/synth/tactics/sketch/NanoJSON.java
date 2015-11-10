package synth.tactics.sketch;

import java.util.List;

public class NanoJson {

    public static String toJson(String s)
    {
        return "\"" + s + "\"";
    }

    public static <E> String toJson(List<E> l)
    {
        StringBuilder b = new StringBuilder();
        for (E element: l) {
            if (b.length() > 0) b.append(", ");
            b.append(toJson(element));
        }
        return "[" + b + "]";
    }

    public static String toJson(Object o)
    {
        if      (o instanceof List<?>)  { return toJson((List<?>)o); }
        else if (o instanceof String)   { return toJson((String)o); }
        else
            return "??";
    }

}
