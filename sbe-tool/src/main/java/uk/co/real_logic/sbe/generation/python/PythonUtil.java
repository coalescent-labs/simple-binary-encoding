/*
 * Copyright 2013-2024 Real Logic Limited.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package uk.co.real_logic.sbe.generation.python;

import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.nio.ByteOrder;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.util.EnumMap;
import java.util.HashMap;
import java.util.Map;
import org.agrona.Strings;
import uk.co.real_logic.sbe.PrimitiveType;
import uk.co.real_logic.sbe.SbeTool;
import uk.co.real_logic.sbe.generation.Generators;
import uk.co.real_logic.sbe.ir.Token;

/**
 * Utilities for mapping between {@link uk.co.real_logic.sbe.ir.Ir} and the Python language.
 */
public class PythonUtil
{
    /**
     * Separator symbols for {@link Object#toString()} implementations on codecs.
     */
    enum Separator
    {
        /**
         * Begin Group symbol.
         */
        BEGIN_GROUP('['),

        /**
         * End Group symbol.
         */
        END_GROUP(']'),

        /**
         * Begin Composite symbol.
         */
        BEGIN_COMPOSITE('('),

        /**
         * End Composite symbol.
         */
        END_COMPOSITE(')'),

        /**
         * Begin Set symbol.
         */
        BEGIN_SET('{'),

        /**
         * End Set symbol.
         */
        END_SET('}'),

        /**
         * Begin Array symbol.
         */
        BEGIN_ARRAY('['),

        /**
         * End Array symbol.
         */
        END_ARRAY(']'),

        /**
         * Field symbol.
         */
        FIELD('|'),

        /**
         * Key Value symbol.
         */
        KEY_VALUE('='),

        /**
         * Entry symbol.
         */
        ENTRY(',');

        private final char symbol;

        Separator(final char symbol)
        {
            this.symbol = symbol;
        }

        void appendToGeneratedBuilder(final StringBuilder builder, final String indent)
        {
            builder.append(indent).append("string_to_append.append('").append(symbol).append("')").append('\n');
        }

        /**
         * {@inheritDoc}
         */
        public String toString()
        {
            return String.valueOf(symbol);
        }
    }

    private static final Map<PrimitiveType, String> TYPE_NAME_BY_PRIMITIVE_TYPE_MAP =
        new EnumMap<>(PrimitiveType.class);

    static
    {
        TYPE_NAME_BY_PRIMITIVE_TYPE_MAP.put(PrimitiveType.CHAR, "bytes");
        TYPE_NAME_BY_PRIMITIVE_TYPE_MAP.put(PrimitiveType.INT8, "int");
        TYPE_NAME_BY_PRIMITIVE_TYPE_MAP.put(PrimitiveType.INT16, "int");
        TYPE_NAME_BY_PRIMITIVE_TYPE_MAP.put(PrimitiveType.INT32, "int");
        TYPE_NAME_BY_PRIMITIVE_TYPE_MAP.put(PrimitiveType.INT64, "int");
        TYPE_NAME_BY_PRIMITIVE_TYPE_MAP.put(PrimitiveType.UINT8, "int");
        TYPE_NAME_BY_PRIMITIVE_TYPE_MAP.put(PrimitiveType.UINT16, "int");
        TYPE_NAME_BY_PRIMITIVE_TYPE_MAP.put(PrimitiveType.UINT32, "int");
        TYPE_NAME_BY_PRIMITIVE_TYPE_MAP.put(PrimitiveType.UINT64, "int");
        TYPE_NAME_BY_PRIMITIVE_TYPE_MAP.put(PrimitiveType.FLOAT, "float");
        TYPE_NAME_BY_PRIMITIVE_TYPE_MAP.put(PrimitiveType.DOUBLE, "float");
    }

    /**
     * Indexes known charset aliases to the name of the instance in {@link StandardCharsets}.
     */
    static final HashMap<String, String> STD_CHARSETS = new HashMap<>();

    static
    {
        try
        {
            for (final Field field : StandardCharsets.class.getDeclaredFields())
            {
                if (Charset.class.isAssignableFrom(field.getType()) && Modifier.isStatic(field.getModifiers()) &&
                    Modifier.isPublic(field.getModifiers()))
                {
                    final Charset charset = (Charset)field.get(null);
                    final String name = field.getName();
                    String oldName = STD_CHARSETS.put(charset.name(), name);

                    if (null != oldName)
                    {
                        throw new IllegalStateException("Duplicate charset alias: old=" + oldName + ", new=" + name);
                    }

                    for (final String alias : charset.aliases())
                    {
                        oldName = STD_CHARSETS.put(alias, name);
                        if (null != oldName)
                        {
                            throw new IllegalStateException(
                                "Duplicate charset alias: old=" + oldName + ", new=" + alias);
                        }
                    }
                }
            }
        }
        catch (final IllegalAccessException ex)
        {
            throw new RuntimeException(ex);
        }
    }

    /**
     * Map the name of a {@link PrimitiveType} to a Python primitive type name.
     *
     * @param primitiveType to map.
     * @return the name of the Python primitive that most closely maps.
     */
    public static String pythonTypeName(final PrimitiveType primitiveType)
    {
        return TYPE_NAME_BY_PRIMITIVE_TYPE_MAP.get(primitiveType);
    }

    /**
     * Format a property name for generated code.
     * <p>
     * If the formatted property name is a keyword then {@link SbeTool#KEYWORD_APPEND_TOKEN} is appended if set.
     *
     * @param value to be formatted.
     * @return the string formatted as a property name.
     * @throws IllegalStateException if a keyword and {@link SbeTool#KEYWORD_APPEND_TOKEN} is not set.
     */
    public static String formatPropertyName(final String value)
    {
        if (value == null)
        {
            return null;
        }

        return value.trim()
            .replaceAll("([a-z])([A-Z]+)", "$1_$2") // Transform camelCase to snake_case
            .toLowerCase()
            .replaceAll("\\s+", "_"); // Replace spaces with underscores
    }

    /**
     * Format a class name for the generated code.
     *
     * @param className to be formatted.
     * @return the formatted class name.
     */
    public static String formatClassName(final String className)
    {
        return Generators.toUpperFirstChar(className);
    }

    /**
     * Shortcut to append a line of generated code.
     *
     * @param builder string builder to which to append the line
     * @param indent  current text indentation
     * @param line    line to be appended
     */
    public static void append(final StringBuilder builder, final String indent, final String line)
    {
        builder.append(indent).append(line).append('\n');
    }

    /**
     * Code to fetch an instance of {@link Charset} corresponding to the given encoding.
     *
     * @param encoding as a string name (eg. UTF-8).
     * @return the code to fetch the associated Charset.
     */
    public static String charset(final String encoding)
    {
        final String charsetName = STD_CHARSETS.get(encoding);
        if (null != charsetName)
        {
            return charsetName;
        }
        else
        {
            final String canonicalName = Charset.isSupported(encoding) ? Charset.forName(encoding).name() : encoding;
            return "java.nio.charset.Charset.forName(\"" + canonicalName + "\")";
        }
    }

    /**
     * Code to fetch the name of the {@link Charset} given the encoding.
     *
     * @param encoding as a string name (eg. UTF-8).
     * @return the code to fetch the associated Charset name.
     */
    public static String charsetName(final String encoding)
    {
        final String charsetName = STD_CHARSETS.get(encoding);
        if (null != charsetName)
        {
            return charsetName;
        }
        else
        {
            return "\"" + (Charset.isSupported(encoding) ? Charset.forName(encoding).name() : encoding) + "\"";
        }
    }

    /**
     * Checks if the given encoding represents an ASCII charset.
     *
     * @param encoding as a string name (e.g. ASCII).
     * @return {@code true} if the encoding denotes an ASCII charset.
     */
    public static boolean isAsciiEncoding(final String encoding)
    {
        return "US_ASCII".equals(STD_CHARSETS.get(encoding));
    }

    /**
     * Checks if the given encoding represents a UTF-8 charset.
     *
     * @param encoding as a string name (e.g. unicode-1-1-utf-8).
     * @return {@code true} if the encoding denotes a UTF-8 charset.
     */
    public static boolean isUtf8Encoding(final String encoding)
    {
        return "UTF_8".equals(STD_CHARSETS.get(encoding));
    }

    /**
     * Generate a literal value to be used in code generation.
     *
     * @param type  of the lateral value.
     * @param value of the lateral.
     * @return a String representation of the Java literal.
     */
    public static String generateLiteral(final PrimitiveType type, final String value)
    {
        String literal = "";

        switch (type)
        {
            case CHAR:
                literal = "b'" + value + "'";
                break;

            case UINT8:
            case INT8:
            case INT16:
            case UINT16:
            case INT32:
            case UINT32:
            case INT64:
            case UINT64:
                literal = value;
                break;

            case FLOAT:
            case DOUBLE:
                if (value.endsWith("NaN"))
                {
                    literal = "float('nan')";
                }
                else
                {
                    literal = value;
                }
                break;
        }

        return literal;
    }

    /**
     * Generate a byte order code for Python struct library to be used in code generation.
     *
     * @param byteOrder .
     * @return a String representation of the Python struct byte order.
     */
    public static String generateStructByteOrderCode(final ByteOrder byteOrder)
    {
        return byteOrder == ByteOrder.LITTLE_ENDIAN ? "<" : ">";
    }

    /**
     * Generate a format code for Python struct library to be used in code generation.
     *
     * @param type .
     * @return a String representation of the Python struct format code.
     */
    public static String generateStructFormatCode(final PrimitiveType type)
    {
        return switch (type)
        {
            case CHAR -> "c";
            case INT8 -> "b";
            case UINT8 -> "B";
            case INT16 -> "h";
            case UINT16 -> "H";
            case INT32 -> "i";
            case UINT32 -> "I";
            case INT64 -> "q";
            case UINT64 -> "Q";
            case FLOAT -> "f";
            case DOUBLE -> "d";
            default -> throw new IllegalArgumentException("primitive type not supported: " + type);
        };
    }

    /**
     * Generate the reStructuredText comment header for a type.
     *
     * @param sb        to append to.
     * @param indent    level for the comment.
     * @param typeToken for the type.
     */
    public static void generateTypeReStructuredText(final StringBuilder sb, final String indent, final Token typeToken)
    {
        final String description = typeToken.description();
        if (Strings.isEmpty(description))
        {
            return;
        }

        sb.append('\n')
            .append(indent).append("\"\"\"\n");

        sb.append(indent).append(description);

        sb.append('\n')
            .append(indent).append(" \"\"\"\n");
    }

    /**`
     * Generate the reStructuredText comment header for a bitset choice option decode method.
     *
     * @param out         to append to.
     * @param indent      level for the comment.
     * @param optionToken for the type.
     * @throws IOException on failing to write to output.
     */
    public static void generateOptionDecodeReStructuredText(final Appendable out,
        final String indent,
        final Token optionToken) throws IOException
    {
        final String description = optionToken.description();
        if (Strings.isEmpty(description))
        {
            return;
        }

        out.append(indent).append("\"\"\"\n");

        out.append(indent).append(description);

        out.append('\n')
            .append(indent).append(":return: true if ").append(optionToken.name()).append(" set or false if not.\n")
            .append(indent).append(" \"\"\"\n");
    }

    /**
     * Generate the reStructuredText comment header for a bitset choice option encode method.
     *
     * @param out         to append to.
     * @param indent      level for the comment.
     * @param optionToken for the type.
     * @throws IOException on failing to write to output.
     */
    public static void generateOptionEncodeReStructuredText(final Appendable out,
        final String indent,
        final Token optionToken) throws IOException
    {
        final String description = optionToken.description();
        if (Strings.isEmpty(description))
        {
            return;
        }

        out.append(indent).append("\"\"\"\n");

        out.append(indent).append(description);

        final String name = optionToken.name();
        out.append('\n')
            .append(indent).append(":param").append(name).append(": value true if is set or false if not.\n")
            .append(indent).append(":return: this for a fluent API.\n")
            .append(indent).append(" \"\"\"\n");
    }

    /**
     * Generate the reStructuredText comment header for flyweight property.
     *
     * @param sb            to append to.
     * @param indent        level for the comment.
     * @param propertyToken for the property name.
     * @param typeName      for the property type.
     */
    public static void generateFlyweightPropertyReStructuredText(
        final StringBuilder sb, final String indent, final Token propertyToken, final String typeName)
    {
        final String description = propertyToken.description();
        if (Strings.isEmpty(description))
        {
            return;
        }

        sb.append('\n')
            .append(indent).append("\"\"\"\n");

        sb.append(indent).append(description);

        sb.append('\n')
            .append(indent).append(":return: ").append(typeName).append(".");

        sb.append(indent).append(description);

        sb.append("\n")
            .append(indent).append("\"\"\"");
    }

    /**
     * Generate the reStructuredText comment header for group encode property.
     *
     * @param sb            to append to.
     * @param indent        level for the comment.
     * @param propertyToken for the property name.
     * @param typeName      for the property type.
     */
    public static void generateGroupEncodePropertyReStructuredText(
        final StringBuilder sb, final String indent, final Token propertyToken, final String typeName)
    {
        final String description = propertyToken.description();
        if (Strings.isEmpty(description))
        {
            return;
        }

        sb.append('\n')
            .append(indent).append("\"\"\"\n");

        sb.append(indent).append(description);

        sb.append("\n")
            .append(indent).append(":param: count of times the group will be encoded.\n")
            .append(indent).append(":return ").append(typeName).append(" : encoder for the group.\n")
            .append(indent).append(" \"\"\"");
    }

}
