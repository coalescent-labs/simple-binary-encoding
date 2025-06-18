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

import static uk.co.real_logic.sbe.generation.python.PythonGenerator.CodecType.DECODER;
import static uk.co.real_logic.sbe.generation.python.PythonGenerator.CodecType.ENCODER;
import static uk.co.real_logic.sbe.generation.python.PythonUtil.Separator;
import static uk.co.real_logic.sbe.generation.python.PythonUtil.append;
import static uk.co.real_logic.sbe.generation.python.PythonUtil.charset;
import static uk.co.real_logic.sbe.generation.python.PythonUtil.charsetName;
import static uk.co.real_logic.sbe.generation.python.PythonUtil.formatClassName;
import static uk.co.real_logic.sbe.generation.python.PythonUtil.formatPropertyName;
import static uk.co.real_logic.sbe.generation.python.PythonUtil.generateFlyweightPropertyReStructuredText;
import static uk.co.real_logic.sbe.generation.python.PythonUtil.generateGroupEncodePropertyReStructuredText;
import static uk.co.real_logic.sbe.generation.python.PythonUtil.generateLiteral;
import static uk.co.real_logic.sbe.generation.python.PythonUtil.generateOptionDecodeReStructuredText;
import static uk.co.real_logic.sbe.generation.python.PythonUtil.generateOptionEncodeReStructuredText;
import static uk.co.real_logic.sbe.generation.python.PythonUtil.generateStructByteOrderCode;
import static uk.co.real_logic.sbe.generation.python.PythonUtil.generateTypeReStructuredText;
import static uk.co.real_logic.sbe.generation.python.PythonUtil.generateStructFormatCode;
import static uk.co.real_logic.sbe.generation.python.PythonUtil.isAsciiEncoding;
import static uk.co.real_logic.sbe.generation.python.PythonUtil.pythonTypeName;
import static uk.co.real_logic.sbe.ir.GenerationUtil.collectFields;
import static uk.co.real_logic.sbe.ir.GenerationUtil.collectGroups;
import static uk.co.real_logic.sbe.ir.GenerationUtil.collectVarData;
import static uk.co.real_logic.sbe.ir.GenerationUtil.findEndSignal;
import static uk.co.real_logic.sbe.ir.GenerationUtil.findSignal;
import static uk.co.real_logic.sbe.ir.GenerationUtil.findSubGroupNames;
import static uk.co.real_logic.sbe.ir.GenerationUtil.getMessageBody;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Formatter;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import org.agrona.Strings;
import org.agrona.Verify;
import org.agrona.generation.OutputManager;
import org.agrona.sbe.CompositeDecoderFlyweight;
import org.agrona.sbe.CompositeEncoderFlyweight;
import org.agrona.sbe.Flyweight;
import org.agrona.sbe.MessageDecoderFlyweight;
import org.agrona.sbe.MessageEncoderFlyweight;
import uk.co.real_logic.sbe.PrimitiveType;
import uk.co.real_logic.sbe.generation.CodeGenerator;
import uk.co.real_logic.sbe.generation.Generators;
import uk.co.real_logic.sbe.ir.Encoding;
import uk.co.real_logic.sbe.ir.HeaderStructure;
import uk.co.real_logic.sbe.ir.Ir;
import uk.co.real_logic.sbe.ir.Signal;
import uk.co.real_logic.sbe.ir.Token;

/**
 * Generate codecs for the Python programming language.
 */
@SuppressWarnings("MethodLength")
public class PythonGenerator implements CodeGenerator
{

    enum CodecType
    {
        /**
         * Decoder type.
         */
        DECODER,
        /**
         * Encoder type.
         */
        ENCODER
    }

    private static final String META_ATTRIBUTE_ENUM = "MetaAttribute";
    private static final String BASE_INDENT = "";
    private static final String INDENT = "    ";

    private final Ir ir;
    private final OutputManager outputManager;

    /**
     * Should the generated code support generating interfaces for the types?
     * if true Flyghweigh interfaces will be used instead of the concrete types.
     */
    private final boolean shouldGenerateInterfaces = false;
    private final boolean shouldDecodeUnknownEnumValues = false;
    private final boolean shouldGenerateGroupOrderAnnotation = false;
    private final boolean shouldImportsGroupsInIndexFile = true;

    /**
     * Create a new Python language {@link CodeGenerator}.
     *
     * @param ir            for the messages and types.
     * @param outputManager for generating the codecs to.
     */
    public PythonGenerator(final Ir ir, final OutputManager outputManager)
    {
        Verify.notNull(ir, "ir");
        Verify.notNull(outputManager, "outputManager");

        this.ir = ir;
        this.outputManager = outputManager;
    }

    /**
     * Generate the composites for dealing with the message header.
     *
     * @throws IOException if an error is encountered when writing the output.
     */
    public void generateMessageHeaderStub() throws IOException
    {
        generateComposite(ir.headerStructure().tokens());
    }

    /**
     * Generate the stubs for the types used as message fields.
     *
     * @throws IOException if an error is encountered when writing the output.
     */
    public void generateTypeStubs() throws IOException
    {
        for (final List<Token> tokens : ir.types())
        {
            switch (tokens.get(0).signal())
            {
                case BEGIN_ENUM:
                    generateEnum(tokens);
                    break;

                case BEGIN_SET:
                    generateBitSet(tokens);
                    break;

                case BEGIN_COMPOSITE:
                    generateComposite(tokens);
                    break;

                default:
                    break;
            }
        }

        generateMetaAttributeEnum();
    }

    /**
     * {@inheritDoc}
     */
    public void generate() throws IOException
    {
        generateTypeStubs();
        generateMessageHeaderStub();

        try (Writer out = outputManager.createOutput("__init__"))
        {
            out.append("\"\"\" Generated SBE (Simple Binary Encoding) message codec. \"\"\"");
        }

        for (final List<Token> tokens : ir.messages())
        {
            final Token msgToken = tokens.get(0);
            final List<Token> messageBody = getMessageBody(tokens);
            final boolean hasVarData = -1 != findSignal(messageBody, Signal.BEGIN_VAR_DATA);

            int i = 0;
            final List<Token> fields = new ArrayList<>();
            i = collectFields(messageBody, i, fields);

            final List<Token> groups = new ArrayList<>();
            i = collectGroups(messageBody, i, groups);

            final List<Token> varData = new ArrayList<>();
            collectVarData(messageBody, i, varData);

            generateDecoder(msgToken, fields, groups, varData, hasVarData);
            generateEncoder(msgToken, fields, groups, varData, hasVarData);
        }
    }

    private void generateEncoder(
        final Token msgToken,
        final List<Token> fields,
        final List<Token> groups,
        final List<Token> varData,
        final boolean hasVarData)
        throws IOException
    {
        final String className = formatClassName(encoderName(msgToken.name()));
        final String implementsString = implementsInterface(MessageEncoderFlyweight.class.getSimpleName());

        try (Writer out = outputManager.createOutput(className))
        {
            out.append(generateFileHeader(generateCoderImports(msgToken.name(), ENCODER, fields, groups)));

            out.append(generateDeclaration(className, implementsString, msgToken));
            out.append(generateEncoderFlyweightCode(className, msgToken,
                generateConstructorFields(fields, groups, ENCODER)));

            final StringBuilder sb = new StringBuilder();
            final StringBuilder groupClassDeclarationStringBuilder = new StringBuilder();
            generateEncoderFields(sb, className, fields, BASE_INDENT);
            generateEncoderGroups(groupClassDeclarationStringBuilder, sb, className, groups, BASE_INDENT, false);
            generateEncoderVarData(sb, className, varData, BASE_INDENT);

            generateEncoderDisplay(sb, decoderName(msgToken.name()));

            out.append(sb);

            out.append(groupClassDeclarationStringBuilder);
        }
    }

    private void generateDecoder(
        final Token msgToken,
        final List<Token> fields,
        final List<Token> groups,
        final List<Token> varData,
        final boolean hasVarData)
        throws IOException
    {
        final String className = formatClassName(decoderName(msgToken.name()));
        final String implementsString = implementsInterface(MessageDecoderFlyweight.class.getSimpleName());

        try (Writer out = outputManager.createOutput(className))
        {
            out.append(generateFileHeader(generateCoderImports(msgToken.name(), DECODER, fields, groups)));

            if (shouldGenerateGroupOrderAnnotation)
            {
                generateAnnotations(BASE_INDENT, className, groups, out, this::decoderName);
            }
            out.append(generateDeclaration(className, implementsString, msgToken));
            out.append(generateDecoderFlyweightCode(className, msgToken,
                generateConstructorFields(fields, groups, DECODER)));

            final StringBuilder sb = new StringBuilder();
            final StringBuilder groupClassDeclarationStringBuilder = new StringBuilder();
            generateDecoderFields(sb, className, fields, BASE_INDENT);
            generateDecoderGroups(groupClassDeclarationStringBuilder, sb, className, groups, BASE_INDENT, false);
            generateDecoderVarData(sb, varData, BASE_INDENT);

            generateDecoderDisplay(sb, msgToken.name(), fields, groups, varData);
            generateMessageLength(sb, className, true, groups, varData, BASE_INDENT);

            out.append(sb);

            out.append(groupClassDeclarationStringBuilder);
        }
    }

    private void generateDecoderGroups(
        final StringBuilder sb,
        final StringBuilder sbParentClass,
        final String outerClassName,
        final List<Token> tokens,
        final String indent,
        final boolean isSubGroup) throws IOException
    {
        for (int i = 0, size = tokens.size(); i < size; i++)
        {
            final Token groupToken = tokens.get(i);
            if (groupToken.signal() != Signal.BEGIN_GROUP)
            {
                throw new IllegalStateException("tokens must begin with BEGIN_GROUP: token=" + groupToken);
            }

            final int index = i;
            final String groupName = decoderName(formatClassName(groupToken.name()));

            ++i;
            final int groupHeaderTokenCount = tokens.get(i).componentTokenCount();
            i += groupHeaderTokenCount;

            final List<Token> fields = new ArrayList<>();
            i = collectFields(tokens, i, fields);

            final List<Token> groups = new ArrayList<>();
            i = collectGroups(tokens, i, groups);

            final List<Token> varData = new ArrayList<>();
            i = collectVarData(tokens, i, varData);

            generateGroupDecoderProperty(sbParentClass, groupName, groupToken, indent);
            generateTypeReStructuredText(sb, indent, groupToken);

            if (shouldGenerateGroupOrderAnnotation)
            {
                generateAnnotations(indent, groupName, groups, sb, this::decoderName);
            }
            generateGroupDecoderClassHeader(sb, groupName, outerClassName, tokens, fields, groups, index, indent);

            generateDecoderFields(sb, groupName, fields, indent);
            final StringBuilder groupClassDeclarationStringBuilder = new StringBuilder();
            generateDecoderGroups(groupClassDeclarationStringBuilder, sb, outerClassName,
                groups, indent, true);
            generateDecoderVarData(sb, varData, indent);

            appendGroupInstanceDecoderDisplay(sb, fields, groups, varData, indent, groupName);
            generateMessageLength(sb, groupName, false, groups, varData, indent);

            sb.append(groupClassDeclarationStringBuilder);
        }
    }

    private void generateEncoderGroups(
        final StringBuilder sb,
        final StringBuilder sbParentClass,
        final String outerClassName,
        final List<Token> tokens,
        final String indent,
        final boolean isSubGroup) throws IOException
    {
        for (int i = 0, size = tokens.size(); i < size; i++)
        {
            final Token groupToken = tokens.get(i);
            if (groupToken.signal() != Signal.BEGIN_GROUP)
            {
                throw new IllegalStateException("tokens must begin with BEGIN_GROUP: token=" + groupToken);
            }

            final int index = i;
            final String groupName = groupToken.name();
            final String groupClassName = encoderName(groupName);

            ++i;
            final int groupHeaderTokenCount = tokens.get(i).componentTokenCount();
            i += groupHeaderTokenCount;

            final List<Token> fields = new ArrayList<>();
            i = collectFields(tokens, i, fields);

            final List<Token> groups = new ArrayList<>();
            i = collectGroups(tokens, i, groups);

            final List<Token> varData = new ArrayList<>();
            i = collectVarData(tokens, i, varData);

            generateGroupEncoderProperty(sbParentClass, groupName, groupToken, indent, isSubGroup);
            generateTypeReStructuredText(sb, indent, groupToken);

            if (shouldGenerateGroupOrderAnnotation)
            {
                generateAnnotations(indent, groupClassName, groups, sb, this::encoderName);
            }
            generateGroupEncoderClassHeader(sb, groupName, outerClassName, tokens, fields, groups, index, indent);

            generateEncoderFields(sb, groupClassName, fields, indent);
            final StringBuilder groupClassDeclarationStringBuilder = new StringBuilder();
            generateEncoderGroups(groupClassDeclarationStringBuilder, sb,
                outerClassName, groups, indent, true);
            generateEncoderVarData(sb, groupClassName, varData, indent);

            sb.append(groupClassDeclarationStringBuilder);
        }
    }

    private void generateGroupDecoderClassHeader(
        final StringBuilder sb,
        final String groupName,
        final String parentMessageClassName,
        final List<Token> tokens,
        final List<Token> groupFields,
        final List<Token> subGroupTokens,
        final int index,
        final String indent)
    {
        final String className = formatClassName(groupName);
        final int dimensionHeaderLen = tokens.get(index + 1).encodedLength();

        final Token blockLengthToken = Generators.findFirst("blockLength", tokens, index);
        final Token numInGroupToken = Generators.findFirst("numInGroup", tokens, index);

        final PrimitiveType blockLengthType = blockLengthToken.encoding().primitiveType();
        final String blockLengthOffset = "limit + " + blockLengthToken.offset();
        final String blockLengthGet = generateGet(
            blockLengthType, blockLengthOffset, generateStructByteOrderCode(blockLengthToken.encoding().byteOrder()));

        final PrimitiveType numInGroupType = numInGroupToken.encoding().primitiveType();
        final String numInGroupOffset = "limit + " + numInGroupToken.offset();
        final String numInGroupGet = generateGet(
            numInGroupType, numInGroupOffset, generateStructByteOrderCode(numInGroupToken.encoding().byteOrder()));

        generateGroupDecoderClassDeclaration(
            sb,
            groupName,
            parentMessageClassName,
            groupFields,
            findSubGroupNames(subGroupTokens),
            indent,
            dimensionHeaderLen);

        sb.append("\n")
            .append(indent).append("    def wrap(self, buffer: bytearray").append("):\n")
            .append(indent).append("        if buffer != self._buffer:\n")
            .append(indent).append("            self._buffer = buffer\n\n")
            .append(indent).append("        self._index = 0\n")
            .append(indent).append("        limit = self._parent_message.get_limit()\n")
            .append(indent).append("        self._parent_message.set_limit(")
            .append("limit + ").append(className).append(".HEADER_SIZE)\n")
            .append(indent).append("        self._block_length = ")
            .append(blockLengthGet).append("\n")
            .append(indent).append("        self._count = ").append(numInGroupGet).append("\n");

        sb.append("\n")
            .append(indent).append("    def __next__(self):\n")
            .append(indent).append("        if self._index >= self._count:\n")
            .append(indent).append("            raise StopIteration\n\n")
            .append(indent).append("        self._offset = self._parent_message.get_limit()\n")
            .append(indent).append("        self._parent_message.set_limit(self._offset + self._block_length)\n")
            .append(indent).append("        self._index+=1\n\n")
            .append(indent).append("        return self\n");

        final String numInGroupJavaTypeName = pythonTypeName(numInGroupType);
        final String numInGroupMinValue = generateLiteral(
            numInGroupType, numInGroupToken.encoding().applicableMinValue().toString());
        generatePrimitiveFieldMetaMethod(sb, indent, numInGroupJavaTypeName, "count", "_min", numInGroupMinValue);
        final String numInGroupMaxValue = generateLiteral(
            numInGroupType, numInGroupToken.encoding().applicableMaxValue().toString());
        generatePrimitiveFieldMetaMethod(sb, indent, numInGroupJavaTypeName, "count", "_max", numInGroupMaxValue);

        sb.append("\n")
            .append(indent).append("    @staticmethod\n")
            .append(indent).append("    def sbe_header_size() -> int:\n")
            .append(indent).append("        return ").append(className).append(".HEADER_SIZE\n");

        sb.append("\n")
            .append(indent).append("    @staticmethod\n")
            .append(indent).append("    def sbe_block_length() -> int:\n")
            .append(indent).append("        return ").append(tokens.get(index).encodedLength()).append("\n");

        sb.append("\n")
            .append(indent).append("    def acting_block_length(self) -> int:\n")
            .append(indent).append("        return self._block_length\n\n")
            .append(indent).append("    def count(self) -> int:\n")
            .append(indent).append("        return self._count\n\n")
            .append(indent).append("    def __iter__(self):\n")
            .append(indent).append("        return self\n\n")
            .append(indent).append("    def remove(self):\n")
            .append(indent).append("        raise Exception(\"UnsupportedOperationException\")\n\n")
            .append(indent).append("    def has_next(self) -> bool:\n")
            .append(indent).append("        return self._index < self._count\n\n");
    }

    private void generateGroupEncoderClassHeader(
        final StringBuilder sb,
        final String groupName,
        final String parentMessageClassName,
        final List<Token> tokens,
        final List<Token> groupFields,
        final List<Token> subGroupTokens,
        final int index,
        final String ind)
    {
        final int dimensionHeaderSize = tokens.get(index + 1).encodedLength();

        generateGroupEncoderClassDeclaration(
            sb,
            groupName,
            parentMessageClassName,
            groupFields,
            findSubGroupNames(subGroupTokens),
            ind,
            dimensionHeaderSize);

        final int blockLength = tokens.get(index).encodedLength();
        final Token blockLengthToken = Generators.findFirst("blockLength", tokens, index);
        final Token numInGroupToken = Generators.findFirst("numInGroup", tokens, index);

        final PrimitiveType blockLengthType = blockLengthToken.encoding().primitiveType();
        final String blockLengthOffset = "limit + " + blockLengthToken.offset();
        final String blockLengthValue = Integer.toString(blockLength);
        final String blockLengthPut = generatePut(
            blockLengthType, blockLengthOffset, blockLengthValue,
            generateStructByteOrderCode(blockLengthToken.encoding().byteOrder()));

        final PrimitiveType numInGroupType = numInGroupToken.encoding().primitiveType();

        final PrimitiveType numInGroupTypeCast = PrimitiveType.UINT32 == numInGroupType ?
            PrimitiveType.INT32 : numInGroupType;
        final String numInGroupOffset = "limit + " + numInGroupToken.offset();
        final String numInGroupValue = "self._count";
        final String numInGroupPut = generatePut(
            numInGroupTypeCast, numInGroupOffset, numInGroupValue,
            generateStructByteOrderCode(numInGroupToken.encoding().byteOrder()));

        final String groupClassName = encoderName(groupName);

        new Formatter(sb).format("\n" +
            ind + "    def wrap(self, buffer: bytearray, count: int):\n" +
            ind + "        if count < %2$d or count > %3$d:\n" +
            ind + "            raise IndexError(\"count outside allowed range: count=\" + str(count))\n\n" +
            ind + "        if buffer != self._buffer:\n" +
            ind + "            self._buffer = buffer\n\n" +
            ind + "        self._index = 0\n" +
            ind + "        self._count = count\n" +
            ind + "        limit = self._parent_message.get_limit()\n" +
            ind + "        self._initial_limit = limit\n" +
            ind + "        self._parent_message.set_limit(limit + " + groupClassName + ".HEADER_SIZE)\n" +
            ind + "        %4$s\n" +
            ind + "        %5$s\n",
            parentMessageClassName,
            numInGroupToken.encoding().applicableMinValue().longValue(),
            numInGroupToken.encoding().applicableMaxValue().longValue(),
            blockLengthPut,
            numInGroupPut);

        sb.append("\n")
            .append(ind).append("    def next(self) -> \"").append(encoderName(groupName)).append("\":\n")
            .append(ind).append("        if self._index >= self._count:\n")
            .append(ind).append("            raise Exception(\"NoSuchElementException\")\n\n")
            .append(ind).append("        self._offset = self._parent_message.get_limit()\n")
            .append(ind).append("        self._parent_message.set_limit(self._offset + ")
            .append(encoderName(groupName)).append(".sbe_block_length())\n")
            .append(ind).append("        self._index+=1\n\n")
            .append(ind).append("        return self\n");

        final String countOffset = "self._initial_limit + " + numInGroupToken.offset();
        final String resetCountPut = generatePut(
            numInGroupTypeCast, countOffset, numInGroupValue,
            generateStructByteOrderCode(numInGroupToken.encoding().byteOrder()));

        sb.append("\n")
            .append(ind).append("    def reset_count_to_index(self) -> int:\n")
            .append(ind).append("        self._count = self._index\n")
            .append(ind).append("        ").append(resetCountPut).append("\n\n")
            .append(ind).append("        return self._count\n");

        final String numInGroupJavaTypeName = pythonTypeName(numInGroupType);
        final String numInGroupMinValue = generateLiteral(
            numInGroupType, numInGroupToken.encoding().applicableMinValue().toString());
        generatePrimitiveFieldMetaMethod(sb, ind, numInGroupJavaTypeName, "count", "_min", numInGroupMinValue);
        final String numInGroupMaxValue = generateLiteral(
            numInGroupType, numInGroupToken.encoding().applicableMaxValue().toString());
        generatePrimitiveFieldMetaMethod(sb, ind, numInGroupJavaTypeName, "count", "_max", numInGroupMaxValue);

        sb.append("\n")
            .append(ind).append("    @staticmethod\n")
            .append(ind).append("    def sbe_header_size() -> int:\n")
            .append(ind).append("        return ").append(groupClassName).append(".HEADER_SIZE\n");

        sb.append("\n")
            .append(ind).append("    @staticmethod\n")
            .append(ind).append("    def sbe_block_length() -> int:\n")
            .append(ind).append("        return ").append(blockLength).append("\n");
    }

    private static String primitiveTypeName(final Token token)
    {
        return pythonTypeName(token.encoding().primitiveType());
    }

    private void generateGroupDecoderClassDeclaration(
        final StringBuilder sb,
        final String groupName,
        final String parentMessageClassName,
        final List<Token> groupFields,
        final List<String> subGroupNames,
        final String indent,
        final int dimensionHeaderSize)
    {
        final String className = formatClassName(groupName);

        new Formatter(sb).format("\n" +
            indent + "class %1$s:\n" +
            indent + "    HEADER_SIZE: int = %2$d\n\n",
            className,
            dimensionHeaderSize);
        sb
            .append("\n")
            .append(indent).append("    ")
            .append("def __init__(self, parent_message: ").append(parentMessageClassName).append("):\n")
            .append(indent).append("        self._parent_message = parent_message\n")
            .append(indent).append("        self._count: int = 0\n")
            .append(indent).append("        self._index: int = 0\n")
            .append(indent).append("        self._buffer: bytearray | None= None\n")
            .append(indent).append("        self._offset: int = 0\n")
            .append(indent).append("        self._block_length: int = 0\n\n");


        Generators.forEachField(
            groupFields,
            (fieldToken, typeToken) ->
            {
                final String propertyName = formatPropertyName(fieldToken.name());
                final String typeName = decoderName(typeToken.name());

                if (typeToken.signal() == Signal.BEGIN_COMPOSITE || typeToken.signal() == Signal.BEGIN_SET)
                {
                    sb
                        .append(indent).append("        self._")
                        .append(propertyName).append(" = ").append(typeName).append("()\n");
                }
            });

        sb.append(indent).append("\n");

        for (final String subGroupName : subGroupNames)
        {
            final String type = formatClassName(decoderName(subGroupName));
            final String field = formatPropertyName(subGroupName);
            sb
                .append(indent).append("        self._")
                .append(field).append(" = ").append(type).append("(parent_message)\n");
        }

        sb.append("\n")
            .append(indent).append("    def parent_message(self) -> ").append(parentMessageClassName).append(":\n")
            .append(indent).append("        return self._parent_message\n");

        generateGroupBufferMethod(sb);
        generateGroupOffsetGetAndSet(sb);
        generateGroupIndexGetAndSet(sb);
        generateGroupCountGetAndSet(sb);
    }

    private void generateGroupBufferMethod(final StringBuilder sb)
    {
        sb.append("""

                def buffer(self) -> bytearray:
                       if self._buffer is None:
                           raise ValueError("buffer is None")

                       return self._buffer

            """);
    }

    private void generateGroupOffsetGetAndSet(final StringBuilder sb)
    {
        sb.append("""

                def get_offset(self) -> int:
                   return self._offset
            """);
        sb.append("""

                def set_offset(self, value: int):
                   self._offset = value
            """);
    }

    private void generateGroupIndexGetAndSet(final StringBuilder sb)
    {
        sb.append("""

                def get_index(self) -> int:
                   return self._index

            """);
        sb.append("""

                def set_index(self, value: int):
                   self._index = value
            """);
    }

    private void generateGroupCountGetAndSet(final StringBuilder sb)
    {
        sb.append("""

                def get_count(self) -> int:
                   return self._count
            """);
        sb.append("""

                def set_count(self, value: int):
                   self._count = value
            """);
    }

    private void generateGroupEncoderClassDeclaration(
        final StringBuilder sb,
        final String groupName,
        final String parentMessageClassName,
        final List<Token> groupFields,
        final List<String> subGroupNames,
        final String indent,
        final int dimensionHeaderSize)
    {
        final String className = encoderName(groupName);

        new Formatter(sb).format("\n" +
            indent + "class %1$s:\n" +
            indent + "    HEADER_SIZE: int = %2$d\n",
            className,
            dimensionHeaderSize);

        sb
            .append("\n")
            .append(indent).append("    ")
            .append("def __init__(self, parent_message: ").append(parentMessageClassName).append("):\n")
            .append(indent).append("        self._parent_message = parent_message\n")
            .append(indent).append("        self._buffer: bytearray | None= None\n")
            .append(indent).append("        self._count: int = 0\n")
            .append(indent).append("        self._index: int = 0\n")
            .append(indent).append("        self._offset: int = 0\n")
            .append(indent).append("        self._initial_limit: int = 0\n\n");

        Generators.forEachField(
            groupFields,
            (fieldToken, typeToken) ->
            {
                final String propertyName = formatPropertyName(fieldToken.name());
                final String typeName = encoderName(typeToken.name());

                if (typeToken.signal() == Signal.BEGIN_COMPOSITE || typeToken.signal() == Signal.BEGIN_SET)
                {
                    sb
                        .append(indent).append("        self._")
                        .append(propertyName).append(" = ").append(typeName).append("()\n");
                }
            });

        sb.append(indent).append("\n");

        for (final String subGroupName : subGroupNames)
        {
            final String type = encoderName(subGroupName);
            final String field = formatPropertyName(subGroupName);
            sb
                .append(indent).append("        self._")
                .append(field).append(" = ").append(type).append("(parent_message)\n");
        }

        generateGroupBufferMethod(sb);
    }

    private static void generateGroupDecoderProperty(
        final StringBuilder sb,
        final String groupName,
        final Token token,
        final String indent)
    {
        final String className = formatClassName(groupName);
        final String propertyName = formatPropertyName(token.name());

        new Formatter(sb).format("\n" +
            indent + "    @staticmethod\n" +
            indent + "    def %s_id() -> int:\n" +
            indent + "        return %d\n",
            formatPropertyName(groupName),
            token.id());

        new Formatter(sb).format("\n" +
            indent + "    @staticmethod\n" +
            indent + "    def %s_since_version() -> int:\n" +
            indent + "        return %d" + "\n",
            formatPropertyName(groupName),
            token.version());

        final String actingVersionGuard = token.version() == 0 ?
            "" :
            indent + "        if self._" + propertyName + ".parent_message().acting_version()" +
            " < " + token.version() + ":\n" +
            indent + "            self._" + propertyName + ".set_count(0)\n" +
            indent + "            self._" + propertyName + ".set_index(0)\n" +
            indent + "            return self._" + propertyName + "\n\n";

        generateFlyweightPropertyReStructuredText(sb, indent + INDENT, token, className);
        new Formatter(sb).format("\n" +
            indent + "    def %2$s(self) -> \"%1$s\":\n" +
            "%3$s" +
            indent + "        self._%2$s.wrap(self.buffer())\n" +
            indent + "        return self._%2$s\n",
            className,
            propertyName,
            actingVersionGuard);
    }

    private void generateGroupEncoderProperty(
        final StringBuilder sb,
        final String groupName,
        final Token token,
        final String indent,
        final boolean isSubGroup)
    {
        final String className = formatClassName(encoderName(groupName));
        final String propertyName = formatPropertyName(groupName);

        new Formatter(sb).format("\n" +
            indent + "    @staticmethod\n" +
            indent + "    def %s_id() -> int:\n" +
            indent + "        return %d\n",
            formatPropertyName(groupName),
            token.id());

        generateGroupEncodePropertyReStructuredText(sb, indent + INDENT, token, className);
        new Formatter(sb).format("\n" +
            indent + "    def %2$s_count(self, count: int) -> \"%1$s\":\n" +
            indent + "        self._%2$s.wrap(self.buffer(), count)\n" +
            indent + "        return self._%2$s\n",
            className,
            propertyName);
    }

    private void generateDecoderVarData(
        final StringBuilder sb, final List<Token> tokens, final String indent)
    {
        for (int i = 0, size = tokens.size(); i < size;)
        {
            final Token token = tokens.get(i);
            if (token.signal() != Signal.BEGIN_VAR_DATA)
            {
                throw new IllegalStateException("tokens must begin with BEGIN_VAR_DATA: token=" + token);
            }

            generateFieldIdMethod(sb, token, indent);
            generateFieldSinceVersionMethod(sb, token, indent);

            final String characterEncoding = tokens.get(i + 3).encoding().characterEncoding();
            generateCharacterEncodingMethod(sb, token.name(), characterEncoding, indent);
            generateFieldMetaAttributeMethod(sb, token, indent);

            final String propertyName = formatPropertyName(token.name());
            final Token lengthToken = tokens.get(i + 2);
            final int sizeOfLengthField = lengthToken.encodedLength();
            final Encoding lengthEncoding = lengthToken.encoding();
            final PrimitiveType lengthType = lengthEncoding.primitiveType();
            final String byteOrderStr = generateStructByteOrderCode(lengthEncoding.byteOrder());

            sb.append("\n")
                .append(indent).append("    @staticmethod\n")
                .append(indent).append("    def ").append(propertyName).append("_header_length() -> int:\n")
                .append(indent).append("        return ").append(sizeOfLengthField).append("\n");

            sb.append("\n")
                .append(indent).append("    def ").append(propertyName).append("_length(self) -> int:\n")
                .append(generateArrayFieldNotPresentCondition(token.version(), indent))
                .append(indent).append("        limit: int = self._parent_message.get_limit()\n")
                .append(indent).append("        return ")
                .append(generateGet(lengthType, "limit", byteOrderStr)).append("\n");

            generateDataDecodeMethods(
                sb, token, propertyName, sizeOfLengthField, lengthType, byteOrderStr, characterEncoding, indent);

            i += token.componentTokenCount();
        }
    }

    private void generateEncoderVarData(
        final StringBuilder sb, final String className, final List<Token> tokens, final String indent)
    {
        for (int i = 0, size = tokens.size(); i < size;)
        {
            final Token token = tokens.get(i);
            if (token.signal() != Signal.BEGIN_VAR_DATA)
            {
                throw new IllegalStateException("tokens must begin with BEGIN_VAR_DATA: token=" + token);
            }

            generateFieldIdMethod(sb, token, indent);
            final Token varDataToken = Generators.findFirst("varData", tokens, i);
            final String characterEncoding = varDataToken.encoding().characterEncoding();
            generateCharacterEncodingMethod(sb, token.name(), characterEncoding, indent);
            generateFieldMetaAttributeMethod(sb, token, indent);

            final String propertyName = formatPropertyName(token.name());
            final Token lengthToken = Generators.findFirst("length", tokens, i);
            final int sizeOfLengthField = lengthToken.encodedLength();
            final Encoding lengthEncoding = lengthToken.encoding();
            final int maxLengthValue = (int)lengthEncoding.applicableMaxValue().longValue();
            final String byteOrderStr = generateStructByteOrderCode(lengthEncoding.byteOrder());

            sb.append("\n")
                .append(indent).append("    @staticmethod\n")
                .append(indent).append("    def ").append(propertyName).append("_header_length() -> int:\n")
                .append(indent).append("        return ")
                .append(sizeOfLengthField).append("\n");

            generateDataEncodeMethods(
                sb,
                propertyName,
                sizeOfLengthField,
                maxLengthValue,
                lengthEncoding.primitiveType(),
                byteOrderStr,
                characterEncoding,
                className,
                indent);

            i += token.componentTokenCount();
        }
    }

    private void generateDataDecodeMethods(
        final StringBuilder sb,
        final Token token,
        final String propertyName,
        final int sizeOfLengthField,
        final PrimitiveType lengthType,
        final String byteOrderStr,
        final String characterEncoding,
        final String indent)
    {
        new Formatter(sb).format("\n" +
            indent + "    def skip_%1$s(self) -> int:\n" +
            "%2$s" +
            indent + "        header_length: int = %3$d\n" +
            indent + "        limit: int = self._parent_message.get_limit()\n" +
            indent + "        data_length: int = %4$s\n" +
            indent + "        data_offset: int = limit + header_length\n" +
            indent + "        self._parent_message.set_limit(data_offset + data_length)\n\n" +
            indent + "        return data_length\n",
            propertyName,
            generateStringNotPresentConditionForAppendable(token.version(), indent),
            sizeOfLengthField,
            generateGet(lengthType, "limit", byteOrderStr));

        generateVarDataTypedDecoder(
            sb,
            token,
            propertyName + "_to_buffer",
            sizeOfLengthField,
            "bytearray",
            lengthType,
            byteOrderStr,
            indent);

        generateVarDataTypedDecoder(
            sb,
            token,
            propertyName + "_to_array",
            sizeOfLengthField,
            "memoryview",
            lengthType,
            byteOrderStr,
            indent);

        generateVarDataWrapDecoder(sb, token, propertyName, sizeOfLengthField, lengthType, byteOrderStr, indent);

        if (null != characterEncoding)
        {
            new Formatter(sb).format("\n" +
                indent + "    def %1$s(self) -> str:\n" +
                "%2$s" +
                indent + "        header_length: int = %3$d\n" +
                indent + "        limit: int = self._parent_message.get_limit()\n" +
                indent + "        data_length: int = %4$s\n" +
                indent + "        self._parent_message.set_limit(limit + header_length + data_length)\n\n" +
                indent + "        if 0 == data_length:\n" +
                indent + "            return \"\"\n\n" +
                indent + "        start = limit + header_length\n" +
                indent + "        end = start + data_length\n" +
                indent + "        raw_bytes = self.buffer()[start: end]\n" +
                indent + "        return raw_bytes.decode('%5$s')\n",
                formatPropertyName(propertyName),
                generateStringNotPresentCondition(token.version(), indent),
                sizeOfLengthField,
                generateGet(lengthType, "limit", byteOrderStr),
                charset(characterEncoding));

            if (isAsciiEncoding(characterEncoding))
            {
                new Formatter(sb).format("\n" +
                    indent + "    def get_%1$s(self, appendable: list[int]) -> int:\n" +
                    "%2$s" +
                    indent + "        header_length: int = %3$d\n" +
                    indent + "        limit: int = self._parent_message.get_limit()\n" +
                    indent + "        data_length: int = %4$s\n" +
                    indent + "        data_offset: int = limit + header_length\n\n" +
                    indent + "        self._parent_message.set_limit(data_offset + data_length)\n" +
                    indent + "        self.buffer()" +
                    ".get_string_ascii(data_offset, data_length, appendable)\n\n" +
                    indent + "        return data_length\n",
                    propertyName,
                    generateStringNotPresentConditionForAppendable(token.version(), indent),
                    sizeOfLengthField,
                    generateGet(lengthType, "limit", byteOrderStr));
            }
        }
    }

    private void generateVarDataWrapDecoder(
        final StringBuilder sb,
        final Token token,
        final String propertyName,
        final int sizeOfLengthField,
        final PrimitiveType lengthType,
        final String byteOrderStr,
        final String indent)
    {
        new Formatter(sb).format("\n" +
            indent + "    def wrap_%s(self, wrap_buffer: bytearray):\n" +
            "%s" +
            indent + "        header_length: int = %d\n" +
            indent + "        limit: int = self._parent_message.get_limit()\n" +
            indent + "        data_length: int = %s\n" +
            indent + "        self._parent_message.set_limit(limit + header_length + data_length)\n" +
            indent + "        start = limit + header_length\n" +
            indent + "        end = start + data_length\n" +
            indent + "        wrap_buffer[:] = self.buffer()[start : end]\n",
            propertyName,
            generateWrapFieldNotPresentCondition(token.version(), indent),
            sizeOfLengthField,
            generateGet(lengthType, "limit", byteOrderStr));
    }

    private void generateDataEncodeMethods(
        final StringBuilder sb,
        final String propertyName,
        final int sizeOfLengthField,
        final int maxLengthValue,
        final PrimitiveType lengthType,
        final String byteOrderStr,
        final String characterEncoding,
        final String className,
        final String indent)
    {
        generateDataTypedEncoder(
            sb,
            className,
            propertyName + "_to_buffer",
            sizeOfLengthField,
            maxLengthValue,
            "bytearray",
            lengthType,
            byteOrderStr,
            indent);

        generateDataTypedEncoder(
            sb,
            className,
            propertyName + "_to_array",
            sizeOfLengthField,
            maxLengthValue,
            "list[int]",
            lengthType,
            byteOrderStr,
            indent);

        if (null != characterEncoding)
        {
            generateCharArrayEncodeMethods(
                sb,
                propertyName,
                sizeOfLengthField,
                maxLengthValue,
                lengthType,
                byteOrderStr,
                characterEncoding,
                className,
                indent);
        }
    }

    private void generateCharArrayEncodeMethods(
        final StringBuilder sb,
        final String propertyName,
        final int sizeOfLengthField,
        final int maxLengthValue,
        final PrimitiveType lengthType,
        final String byteOrderStr,
        final String characterEncoding,
        final String className,
        final String indent)
    {
        final PrimitiveType lengthPutType = PrimitiveType.UINT32 == lengthType ? PrimitiveType.INT32 : lengthType;

        if (isAsciiEncoding(characterEncoding))
        {
            new Formatter(sb).format("\n" +
                indent + "    def %2$s(self, value: str) -> \"%1$s\":\n" +
                indent + "        length: int = 0 if value is None else len(value)\n" +
                indent + "        if length > %3$d:\n" +
                indent + "            raise ValueError(\"length > max_value for type: \" + str(length))\n\n" +
                indent + "        header_length: int = %4$d\n" +
                indent + "        limit: int = self._parent_message.get_limit()\n" +
                indent + "        self._parent_message.set_limit(limit + header_length + length)\n" +
                indent + "        %5$s\n" +
                indent + "        encoded = value.encode(\"%6$s\")\n" +
                indent + "        length = len(encoded)\n" +
                indent + "        self.buffer()[limit + header_length, limit + header_length + length] = encoded\n\n" +
                indent + "        return self\n",
                className,
                formatPropertyName(propertyName),
                maxLengthValue,
                sizeOfLengthField,
                generatePut(lengthPutType, "limit", "length", byteOrderStr),
                charset(characterEncoding));
        }
        else
        {
            new Formatter(sb).format("\n" +
                indent + "    def %2$s(self, value: str) -> \"%1$s\":\n" +
                indent + "        encoded = value.encode(\"%3$s\") if value else b\"\"\n" +
                indent + "        length = len(encoded)\n" +
                indent + "        if length > %4$d:\n" +
                indent + "            raise ValueError(\"length > max_value for type: \" + str(length))\n\n" +
                indent + "        header_length: int = %5$d\n" +
                indent + "        limit: int = self._parent_message.get_limit()\n" +
                indent + "        self._parent_message.set_limit(limit + header_length + length)\n" +
                indent + "        %6$s\n" +
                indent + "        self.buffer()[limit + header_length: limit + header_length + length] = encoded\n\n" +
                indent + "        return self\n",
                className,
                formatPropertyName(propertyName),
                charset(characterEncoding),
                maxLengthValue,
                sizeOfLengthField,
                generatePut(lengthPutType, "limit", "length", byteOrderStr));
        }
    }

    private void generateVarDataTypedDecoder(
        final StringBuilder sb,
        final Token token,
        final String propertyName,
        final int sizeOfLengthField,
        final String exchangeType,
        final PrimitiveType lengthType,
        final String byteOrderStr,
        final String indent)
    {
        new Formatter(sb).format("\n" +
            indent + "    def get_%s(self, dst: %s, dst_offset: int, length: int) -> int:\n" +
            "%s" +
            indent + "        header_length: int = %d\n" +
            indent + "        limit: int = self._parent_message.get_limit()\n" +
            indent + "        data_length: int = %s\n" +
            indent + "        bytes_copied: int = min(length, data_length)\n" +
            indent + "        self._parent_message.set_limit(limit + header_length + data_length)\n" +
            indent + "        start = limit + header_length\n" +
            indent + "        end = start + bytes_copied\n" +
            indent + "        dst[dst_offset: dst_offset + bytes_copied] = self.buffer()[start: end] \n" +
            indent + "        return bytes_copied\n",
            propertyName,
            exchangeType,
            generateArrayFieldNotPresentCondition(token.version(), indent),
            sizeOfLengthField,
            generateGet(lengthType, "limit", byteOrderStr));
    }

    private void generateDataTypedEncoder(
        final StringBuilder sb,
        final String className,
        final String propertyName,
        final int sizeOfLengthField,
        final int maxLengthValue,
        final String exchangeType,
        final PrimitiveType lengthType,
        final String byteOrderStr,
        final String indent)
    {
        final PrimitiveType lengthPutType = PrimitiveType.UINT32 == lengthType ? PrimitiveType.INT32 : lengthType;

        new Formatter(sb).format("\n" +
            indent + "    def put_%2$s(self, src: %3$s, src_offset: int, length: int) -> \"%1$s\":\n" +
            indent + "        if length > %4$d:\n" +
            indent + "            raise ValueError(\"length > max_value for type: \" + str(length))\n\n" +
            indent + "        header_length: int = %5$d\n" +
            indent + "        limit: int = self._parent_message.get_limit()\n" +
            indent + "        self._parent_message.set_limit(limit + header_length + length)\n" +
            indent + "        %6$s\n" +
            indent + "        start = limit + header_length\n" +
            indent + "        end = start + length\n" +
            indent + "        self.buffer()[start: end] = src[src_offset : src_offset + length]\n\n" +
            indent + "        return self\n",
            className,
            propertyName,
            exchangeType,
            maxLengthValue,
            sizeOfLengthField,
            generatePut(lengthPutType, "limit", "length", byteOrderStr));
    }

    private void generateBitSet(final List<Token> tokens) throws IOException
    {
        final Token token = tokens.get(0);
        final String bitSetName = token.applicableTypeName();
        final String decoderName = decoderName(bitSetName);
        final String encoderName = encoderName(bitSetName);
        final List<Token> choiceList = tokens.subList(1, tokens.size() - 1);
        final String implementsString = implementsInterface(Flyweight.class.getSimpleName());

        try (Writer out = outputManager.createOutput(decoderName))
        {
            final Encoding encoding = token.encoding();

            out.append(generateFileHeader(""));
            out.append(generateDeclaration(decoderName, implementsString, token));
            out.append(generateFixedFlyweightCode(decoderName, token.encodedLength(), ""));

            out.append(generateChoiceIsEmpty(encoding.primitiveType()));

            new Formatter(out).format(
                """

                    def get_raw(self) -> %s:
                        return %s

                """,
                primitiveTypeName(token),
                generateGet(encoding.primitiveType(), "self._offset",
                generateStructByteOrderCode(encoding.byteOrder())));

            generateChoiceDecoders(out, choiceList);
            out.append(generateChoiceDisplay(choiceList));
            out.append("\n");
        }

        try (Writer out = outputManager.createOutput(encoderName))
        {
            out.append(generateFileHeader(""));
            out.append(generateDeclaration(encoderName, implementsString, token));
            out.append(generateFixedFlyweightCode(encoderName, token.encodedLength(), ""));
            generateChoiceClear(out, encoderName, token);
            generateChoiceEncoders(out, encoderName, choiceList);
        }
    }

    private void generateEnum(final List<Token> tokens) throws IOException
    {
        final Token enumToken = tokens.get(0);
        final String enumClassName = formatClassName(enumToken.applicableTypeName());
        final Encoding encoding = enumToken.encoding();
        final String nullVal = encoding.applicableNullValue().toString();

        try (Writer out = outputManager.createOutput(enumClassName))
        {
            out.append(generateEnumFileHeader());
            out.append(generateEnumDeclaration(enumClassName, enumToken));

            final List<Token> valuesList = tokens.subList(1, tokens.size() - 1);
            out.append(generateEnumValues(valuesList, nullVal));

            out.append(generateEnumLookupMethod());
        }
    }

    private void generateComposite(final List<Token> tokens) throws IOException
    {
        final Token token = tokens.get(0);
        final String compositeName = token.applicableTypeName();
        final String decoderName = decoderName(compositeName);
        final String encoderName = encoderName(compositeName);

        try (Writer out = outputManager.createOutput(decoderName))
        {
            final String implementsString = implementsInterface(CompositeDecoderFlyweight.class.getSimpleName());
            out.append(generateFileHeader(
                generateCompositeImports(compositeName, DECODER, tokens.subList(1, tokens.size()))));
            out.append(generateDeclaration(decoderName, implementsString, token));
            out.append(generateFixedFlyweightCode(decoderName, token.encodedLength(),
                generateConstructorFields(tokens.subList(1, tokens.size()), new ArrayList<>(), DECODER))
            );

            for (int i = 1, end = tokens.size() - 1; i < end;)
            {
                final Token encodingToken = tokens.get(i);
                final String propertyName = formatPropertyName(encodingToken.name());
                final String typeName = decoderName(encodingToken.applicableTypeName());

                final StringBuilder sb = new StringBuilder();
                generateEncodingOffsetMethod(sb, propertyName, encodingToken.offset(), BASE_INDENT);
                generateEncodingLengthMethod(sb, propertyName, encodingToken.encodedLength(), BASE_INDENT);
                generateFieldSinceVersionMethod(sb, encodingToken, BASE_INDENT);

                switch (encodingToken.signal())
                {
                    case ENCODING:
                        generatePrimitiveDecoder(
                            sb, true, encodingToken.name(), encodingToken, encodingToken, BASE_INDENT, decoderName);
                        break;

                    case BEGIN_ENUM:
                        generateEnumDecoder(sb, true, encodingToken, propertyName, encodingToken, BASE_INDENT);
                        break;

                    case BEGIN_SET:
                        generateBitSetProperty(
                            sb, true, DECODER, propertyName, encodingToken, encodingToken, BASE_INDENT, typeName);
                        break;

                    case BEGIN_COMPOSITE:
                        generateCompositeProperty(
                            sb, true, DECODER, propertyName, encodingToken, encodingToken, BASE_INDENT, typeName);
                        break;

                    default:
                        break;
                }

                out.append(sb);
                i += encodingToken.componentTokenCount();
            }

            out.append(generateCompositeDecoderDisplay(tokens, decoderName));
        }

        try (Writer out = outputManager.createOutput(encoderName))
        {

            final String implementsString = implementsInterface(CompositeEncoderFlyweight.class.getSimpleName());
            out.append(generateFileHeader(
                generateCompositeImports(compositeName, ENCODER, tokens.subList(1, tokens.size())))
            );
            out.append(generateDeclaration(encoderName, implementsString, token));
            out.append(generateFixedFlyweightCode(encoderName, token.encodedLength(),
                generateConstructorFields(tokens.subList(1, tokens.size()), new ArrayList<>(), ENCODER)));

            for (int i = 1, end = tokens.size() - 1; i < end;)
            {
                final Token encodingToken = tokens.get(i);
                final String propertyName = formatPropertyName(encodingToken.name());
                final String typeName = encoderName(encodingToken.applicableTypeName());

                final StringBuilder sb = new StringBuilder();
                generateEncodingOffsetMethod(sb, propertyName, encodingToken.offset(), BASE_INDENT);
                generateEncodingLengthMethod(sb, propertyName, encodingToken.encodedLength(), BASE_INDENT);

                switch (encodingToken.signal())
                {
                    case ENCODING:
                        generatePrimitiveEncoder(sb, encoderName, encodingToken.name(),
                            encodingToken, BASE_INDENT);
                        break;

                    case BEGIN_ENUM:
                        generateEnumEncoder(sb, encoderName, encodingToken,
                            propertyName, encodingToken, BASE_INDENT);
                        break;

                    case BEGIN_SET:
                        generateBitSetProperty(
                            sb, true, ENCODER, propertyName,
                            encodingToken, encodingToken, BASE_INDENT, typeName);
                        break;

                    case BEGIN_COMPOSITE:
                        generateCompositeProperty(
                            sb, true, ENCODER, propertyName,
                            encodingToken, encodingToken, BASE_INDENT, typeName);
                        break;

                    default:
                        break;
                }

                out.append(sb);
                i += encodingToken.componentTokenCount();
            }

            out.append(generateCompositeEncoderDisplay(decoderName));
        }
    }

    private void generateChoiceClear(final Appendable out, final String bitSetClassName, final Token token)
        throws IOException
    {
        final Encoding encoding = token.encoding();
        final String literalValue = generateLiteral(encoding.primitiveType(), "0");
        final String byteOrderStr = generateStructByteOrderCode(encoding.byteOrder());

        out.append(String.format("""
                def clear(self):
                    %1$s
                    return self

            """, generatePut(encoding.primitiveType(), "self._offset", literalValue, byteOrderStr)));
    }

    private void generateChoiceDecoders(final Appendable out, final List<Token> tokens)
        throws IOException
    {
        for (final Token token : tokens)
        {
            if (token.signal() == Signal.CHOICE)
            {
                final String choiceName = formatPropertyName(token.name());
                final Encoding encoding = token.encoding();
                final String choiceBitIndex = encoding.constValue().toString();
                final String byteOrderStr = generateStructByteOrderCode(encoding.byteOrder());
                final PrimitiveType primitiveType = encoding.primitiveType();

                generateOptionDecodeReStructuredText(out, INDENT, token);
                final String choiceGet = generateChoiceGet(primitiveType, choiceBitIndex, byteOrderStr);
                final String staticChoiceGet = generateStaticChoiceGet(choiceBitIndex);
                out.append("\n")
                    .append("    def ").append(choiceName).append("(self) -> bool:\n")
                    .append("        return ").append(choiceGet).append("\n\n\n")
                    .append("    @staticmethod\n")
                    .append("    def ").append(choiceName).append("_static")
                    .append("(value: int) -> bool:\n")
                    .append("        return ").append(staticChoiceGet).append("\n\n");
            }
        }
    }

    private void generateChoiceEncoders(final Appendable out, final String bitSetClassName, final List<Token> tokens)
        throws IOException
    {
        for (final Token token : tokens)
        {
            if (token.signal() == Signal.CHOICE)
            {
                final String choiceName = formatPropertyName(token.name());
                final Encoding encoding = token.encoding();
                final String choiceBitIndex = encoding.constValue().toString();
                final String byteOrderStr = generateStructByteOrderCode(encoding.byteOrder());
                final PrimitiveType primitiveType = encoding.primitiveType();

                generateOptionEncodeReStructuredText(out, INDENT, token);
                final String choicePut = generateChoicePut(encoding.primitiveType(), choiceBitIndex, byteOrderStr);
                final String staticChoicePut = generateStaticChoicePut(encoding.primitiveType(), choiceBitIndex);
                out.append("\n")
                    .append("    def ").append(choiceName)
                    .append("(self, value: bool): ").append("\n")
                    .append(choicePut).append("\n")
                    .append("        return self\n")
                    .append("    \n\n")
                    .append("    @staticmethod\n")
                    .append("    def ").append(choiceName).append("_static")
                    .append("(bits: int, value: bool) -> int").append(":\n")
                    .append("    \n")
                    .append(staticChoicePut);
            }
        }
    }

    private CharSequence generateEnumValues(final List<Token> tokens, final String nullVal)
    {
        final StringBuilder sb = new StringBuilder();

        for (final Token token : tokens)
        {
            final Encoding encoding = token.encoding();
            final String enumAttribute = token.name().equals("None") ? "Null" : token.name();
            sb.append(INDENT).append(enumAttribute).append(" = ")
                .append(encoding.constValue().toString()).append("\n\n");
        }

        if (shouldDecodeUnknownEnumValues)
        {
            sb.append(INDENT).append("# To be used to represent an unknown value from a later version.\n");
            sb.append(INDENT).append("SBE_UNKNOWN").append(" = ").append(nullVal).append("\n\n");
        }

        sb.append(INDENT).append("# To be used to represent not present or null.\n");
        sb.append(INDENT).append("NULL_VAL").append(" = ").append(nullVal).append("\n\n");

        return sb;
    }

    private CharSequence generateEnumLookupMethod()
    {
        final StringBuilder sb = new StringBuilder();

        sb.append("\n").append("""
                @classmethod
                def get(cls, value: int):
                    \"""
                    Look up the enum member from its integer value.
                    Raises ValueError if not found.
                    \"""
                    try:
                        return cls(value)
                    except ValueError:
            """);

        if (shouldDecodeUnknownEnumValues)
        {
            sb.append(INDENT.repeat(2)).append("    return cls.SBE_UNKNOWN;\n");
        }
        else
        {
            sb.append(INDENT.repeat(2)).append(
                "    raise ValueError(f\"{cls.__name__} not found for value: {value}\")");
        }

        return sb;
    }

    private CharSequence generateFileHeader(final String importStatements)
    {

        return String.format("""
            \""" Generated SBE (Simple Binary Encoding) message codec. \"""

            import struct

            %s

            """, importStatements);
    }

    private void generateAnnotations(
        final String indent,
        final String className,
        final List<Token> tokens,
        final Appendable out,
        final Function<String, String> nameMapping) throws IOException
    {
        final List<String> groupClassNames = new ArrayList<>();
        int level = 0;

        for (final Token token : tokens)
        {
            if (token.signal() == Signal.BEGIN_GROUP)
            {
                if (1 == ++level)
                {
                    groupClassNames.add(formatClassName(nameMapping.apply(token.name())));
                }
            }
            else if (token.signal() == Signal.END_GROUP)
            {
                --level;
            }
        }
    }

    private static CharSequence generateDeclaration(
        final String className, final String implementsString, final Token typeToken)
    {
        final StringBuilder sb = new StringBuilder();

        generateTypeReStructuredText(sb, BASE_INDENT, typeToken);
        if (typeToken.deprecated() > 0)
        {
            sb.append("from warnings import deprecated\n\n");
            sb.append("@deprecated(\"\")\n");
        }
        sb
            .append("class ").append(className).append(implementsString).append(":\n");

        return sb;
    }

    private void generateMetaAttributeEnum() throws IOException
    {
        try (Writer out = outputManager.createOutput(META_ATTRIBUTE_ENUM))
        {
            out.append("""
                \""" Generated SBE (Simple Binary Encoding) message codec. \"""

                from enum import IntEnum

                # Meta attribute enum for selecting a particular meta attribute value.

                class MetaAttribute(IntEnum):

                    # The epoch or start of time. Default is 'UNIX' which is midnight 1st January 1970 UTC.
                    EPOCH = 0

                    # Time unit applied to the epoch. Can be second, millisecond, microsecond, or nanosecond.
                    TIME_UNIT = 1

                    # The type relationship to a FIX tag value encoded type. For reference only.
                    SEMANTIC_TYPE = 2

                    # Field presence indication. Can be optional, required, or constant.
                    PRESENCE = 3
                """);
        }
    }

    private static CharSequence generateEnumFileHeader()
    {
        return
            """
                \""" Generated SBE (Simple Binary Encoding) message codec. \"""

                from enum import IntEnum

                """;
    }

    private static CharSequence generateEnumDeclaration(final String name, final Token typeToken)
    {
        final StringBuilder sb = new StringBuilder();

        sb.append("class ").append(name).append("(IntEnum):\n");

        return sb;
    }

    private void generatePrimitiveDecoder(
        final StringBuilder sb,
        final boolean inComposite,
        final String propertyName,
        final Token propertyToken,
        final Token encodingToken,
        final String indent,
        final String containingClassName)
    {
        final String formattedPropertyName = formatPropertyName(propertyName);

        generatePrimitiveFieldMetaMethod(sb, formattedPropertyName, encodingToken, indent);

        if (encodingToken.isConstantEncoding())
        {
            generateConstPropertyMethods(sb, containingClassName, formattedPropertyName, encodingToken, indent);
        }
        else
        {
            sb.append(generatePrimitivePropertyDecodeMethods(
                inComposite, formattedPropertyName, propertyToken, encodingToken, indent));
        }
    }

    private void generatePrimitiveEncoder(
        final StringBuilder sb,
        final String containingClassName,
        final String propertyName,
        final Token token,
        final String indent)
    {
        final String formattedPropertyName = formatPropertyName(propertyName);

        generatePrimitiveFieldMetaMethod(sb, formattedPropertyName, token, indent);

        if (!token.isConstantEncoding())
        {
            sb.append(generatePrimitivePropertyEncodeMethods(
                containingClassName, formattedPropertyName, token, indent));
        }
        else
        {
            generateConstPropertyMethods(sb, containingClassName, formattedPropertyName, token, indent);
        }
    }

    private CharSequence generatePrimitivePropertyDecodeMethods(
        final boolean inComposite,
        final String propertyName,
        final Token propertyToken,
        final Token encodingToken,
        final String indent)
    {
        return encodingToken.matchOnLength(
            () -> generatePrimitivePropertyDecode(inComposite, propertyName, propertyToken, encodingToken, indent),
            () -> generatePrimitiveArrayPropertyDecode(
                inComposite, propertyName, propertyToken, encodingToken, indent));
    }

    private CharSequence generatePrimitivePropertyEncodeMethods(
        final String containingClassName, final String propertyName, final Token token, final String indent)
    {
        return token.matchOnLength(
            () -> generatePrimitivePropertyEncode(containingClassName, propertyName, token, indent),
            () -> generatePrimitiveArrayPropertyEncode(containingClassName, propertyName, token, indent));
    }

    private void generatePrimitiveFieldMetaMethod(
        final StringBuilder sb, final String propertyName, final Token token, final String indent)
    {
        final PrimitiveType primitiveType = token.encoding().primitiveType();
        final String pythonTypeName = pythonTypeName(primitiveType);
        final String formattedPropertyName = formatPropertyName(propertyName);

        final String nullValue = generateLiteral(primitiveType, token.encoding().applicableNullValue().toString());
        generatePrimitiveFieldMetaMethod(sb, indent, pythonTypeName, formattedPropertyName, "_null", nullValue);

        final String minValue = generateLiteral(primitiveType, token.encoding().applicableMinValue().toString());
        generatePrimitiveFieldMetaMethod(sb, indent, pythonTypeName, formattedPropertyName, "_min", minValue);

        final String maxValue = generateLiteral(primitiveType, token.encoding().applicableMaxValue().toString());
        generatePrimitiveFieldMetaMethod(sb, indent, pythonTypeName, formattedPropertyName, "_max", maxValue);
    }

    private void generatePrimitiveFieldMetaMethod(
        final StringBuilder sb,
        final String indent,
        final String pythonTypeName,
        final String formattedPropertyName,
        final String metaType,
        final String retValue)
    {
        sb.append("\n")
            .append(indent).append("    @staticmethod\n")
            .append(indent).append("    def ")
            .append(formattedPropertyName).append(metaType).append("_value() -> ").append(pythonTypeName).append(":\n")
            .append(indent).append("        return ").append(retValue).append("\n");
    }

    private CharSequence generatePrimitivePropertyDecode(
        final boolean inComposite,
        final String propertyName,
        final Token propertyToken,
        final Token encodingToken,
        final String indent)
    {
        final Encoding encoding = encodingToken.encoding();
        final String pythonTypeName = pythonTypeName(encoding.primitiveType());

        final int offset = encodingToken.offset();
        final String byteOrderStr = generateStructByteOrderCode(encoding.byteOrder());

        final CharSequence noPresentCondition = generateFieldNotPresentCondition(inComposite,
            propertyToken.version(), encoding, indent);

        return String.format(
            "\n" +
            indent + "    def %s(self) -> %s:\n" +
            "%s" +
            indent + "        return %s\n\n",
            formatPropertyName(propertyName),
            noPresentCondition.isEmpty() ? pythonTypeName : pythonTypeName + " | None",
            noPresentCondition,
            generateGet(encoding.primitiveType(), "self._offset + " + offset, byteOrderStr));
    }

    private CharSequence generatePrimitivePropertyEncode(
        final String containingClassName, final String propertyName, final Token token, final String indent)
    {
        final Encoding encoding = token.encoding();
        final String pythonTypeName = pythonTypeName(encoding.primitiveType());
        final int offset = token.offset();
        final String byteOrderStr = generateStructByteOrderCode(encoding.byteOrder());

        return String.format(
            "\n" +
            indent + "    def %s(self, value: %s) -> \"%s\":\n" +
            indent + "        %s\n" +
            indent + "        return self\n\n",
            formatPropertyName(propertyName),
            pythonTypeName,
            formatClassName(containingClassName),
            generatePut(encoding.primitiveType(), "self._offset + " + offset, "value", byteOrderStr));
    }

    private CharSequence generateWrapFieldNotPresentCondition(final int sinceVersion, final String indent)
    {
        if (0 == sinceVersion)
        {
            return "";
        }

        return
            indent + "        if self._parent_message.acting_version() < " + sinceVersion + ":\n" +
            indent + "            wrap_buffer[:] = self.buffer()[self._offset : self._offset + 0]\n" +
            indent + "            return\n\n";
    }

    private CharSequence generateFieldNotPresentCondition(
        final boolean inComposite, final int sinceVersion, final Encoding encoding, final String indent)
    {
        if (inComposite || 0 == sinceVersion)
        {
            return "";
        }

        final String nullValue = generateLiteral(encoding.primitiveType(), encoding.applicableNullValue().toString());
        return
            indent + "        if self._parent_message.acting_version() < " + sinceVersion + ":\n" +
            indent + "            return " + nullValue + "\n\n";
    }

    private static CharSequence generateArrayFieldNotPresentCondition(final int sinceVersion, final String indent)
    {
        if (0 == sinceVersion)
        {
            return "";
        }

        return
            indent + "        if self._parent_message.acting_version() < " + sinceVersion + ":\n" +
            indent + "            return 0\n\n";
    }

    private static CharSequence generateStringNotPresentConditionForAppendable(
        final int sinceVersion, final String indent)
    {
        if (0 == sinceVersion)
        {
            return "";
        }

        return
            indent + "        if self._parent_message.acting_version() < " + sinceVersion + ":\n" +
            indent + "            return 0\n\n";
    }

    private static CharSequence generateStringNotPresentCondition(final int sinceVersion, final String indent)
    {
        if (0 == sinceVersion)
        {
            return "";
        }

        return
            indent + "        if self._parent_message.acting_version() < " + sinceVersion + ":\n" +
            indent + "            return \"\"\n\n";
    }

    private static CharSequence generatePropertyNotPresentCondition(
        final boolean inComposite,
        final CodecType codecType,
        final Token propertyToken,
        final String enumName,
        final String indent)
    {
        if (inComposite || codecType == ENCODER || 0 == propertyToken.version())
        {
            return "";
        }

        final String nullValue = enumName == null ? "None" : (enumName + ".NULL_VAL");
        return
            indent + "        if self._parent_message.acting_version() < " + propertyToken.version() + ":\n" +
            indent + "            return " + nullValue + "\n\n";
    }

    private CharSequence generatePrimitiveArrayPropertyDecode(
        final boolean inComposite,
        final String propertyName,
        final Token propertyToken,
        final Token encodingToken,
        final String indent)
    {
        final Encoding encoding = encodingToken.encoding();
        final String pythonTypeName = pythonTypeName(encoding.primitiveType());
        final int offset = encodingToken.offset();
        final String byteOrderStr = generateStructByteOrderCode(encoding.byteOrder());
        final int fieldLength = encodingToken.arrayLength();
        final int typeSize = sizeOfPrimitive(encoding);

        final StringBuilder sb = new StringBuilder();

        generateArrayLengthMethod(propertyName, indent, fieldLength, sb);

        final CharSequence noPresentCondition = generateFieldNotPresentCondition(inComposite,
            propertyToken.version(), encoding, indent);

        new Formatter(sb).format("\n" +
            indent + "    def %s(self, index: int) -> %s:\n" +
            indent + "        if index < 0 or index >= %d:\n" +
            indent + "            raise IndexError(\"index out of range: index=\" + str(index))\n\n" +
            "%s" +
            indent + "        pos: int = self._offset + %d + (index * %d)\n\n" +
            indent + "        return %s\n\n",
            propertyName,
            noPresentCondition.isEmpty() ? pythonTypeName : pythonTypeName + " | None",
            fieldLength,
            noPresentCondition,
            offset,
            typeSize,
            generateGet(encoding.primitiveType(), "pos", byteOrderStr));

        if (encoding.primitiveType() == PrimitiveType.CHAR)
        {
            generateCharacterEncodingMethod(sb, propertyName, encoding.characterEncoding(), indent);

            new Formatter(sb).format("\n" +
                indent + "    def get_%s(self, dst, dst_offset: int) -> int:\n" +
                indent + "        length: int = %d\n" +
                indent + "        if dst_offset < 0 or dst_offset > (len(dst) - length):\n\n" +
                indent + "            raise IndexError(" +
                "\"Copy will go out of range: offset=\" + str(dst_offset))\n\n" +
                "%s" +
                indent + "        start = self._offset + %d\n" +
                indent + "        end = start + length\n" +
                indent + "        dst[dst_offset: dst_offset + length] = self.buffer()[start: end]\n\n" +
                indent + "        return length\n\n",
                propertyName,
                fieldLength,
                generateArrayFieldNotPresentCondition(propertyToken.version(), indent),
                offset);

            new Formatter(sb).format("\n" +
                indent + "    def %s_string(self) -> str:\n" +
                "%s" +
                indent + "        dst = memoryview(self._buffer)[self._offset: self._offset + %d]\n" +
                indent + "        end = next((i for i, b in enumerate(dst) if b == 0), %d)\n" +
                indent + "        return dst[:end].tobytes().decode(\"%s\")\n\n",
                propertyName,
                generateStringNotPresentCondition(propertyToken.version(), indent),
                fieldLength,
                offset,
                charset(encoding.characterEncoding()));

            if (isAsciiEncoding(encoding.characterEncoding()))
            {
                new Formatter(sb).format("\n" +
                    indent + "    def get_%1$s_ascii(self, value: list[int]) -> int:\n" +
                    "%2$s" +
                    indent + "        for i in range(%3$d):\n" +
                    indent + "            c: int = self.buffer()[self._offset + %4$d + i] & 0xFF\n" +
                    indent + "            if c == 0:\n" +
                    indent + "                return i\n\n" +
                    indent + "            try:\n" +
                    indent + "                value.append(ord('?') if c > 127 else c)\n" +
                    indent + "            except Exception as ex:\n" +
                    indent + "                raise ValueError(ex)\n\n" +
                    indent + "        return %3$d\n",
                    propertyName,
                    generateStringNotPresentConditionForAppendable(propertyToken.version(), indent),
                    fieldLength,
                    offset);
            }
        }
        else if (encoding.primitiveType() == PrimitiveType.UINT8)
        {
            new Formatter(sb).format("\n" +
                indent + "    def get_%s(dst: bytearray, dst_offset: int, length: int) -> int:\n" +
                "%s" +
                indent + "        bytes_copied: int = min(length, %d)\n" +
                indent + "        start = self._offset + %d\n" +
                indent + "        end = start + bytes_copied\n" +
                indent + "        dst[dst_offset: dst_offset+ length] = self.buffer()[start: end]\n\n" +
                indent + "        return bytes_copied\n",
                propertyName,
                generateArrayFieldNotPresentCondition(propertyToken.version(), indent),
                fieldLength,
                offset);

            new Formatter(sb).format("\n" +
                indent + "    def get_%s_from_buffer(dst: bytearray, dst_offset: int, length: int) -> int:\n" +
                "%s" +
                indent + "        bytes_copied: int = min(length, %d)\n" +
                indent + "        start = self._offset + %d\n" +
                indent + "        end = start + bytes_copied\n" +
                indent + "        dst[dst_offset: dst_offset+ length] = self.buffer()[start: end]\n\n" +
                indent + "        return bytes_copied\n",
                propertyName,
                generateArrayFieldNotPresentCondition(propertyToken.version(), indent),
                fieldLength,
                offset);

            new Formatter(sb).format("\n" +
                indent + "    def wrap_%s(self, wrap_buffer: bytearray)\n" +
                "%s" +
                indent + "        wrap_buffer.wrap(self.buffer(), self._offset + %d, %d)\n\n" +
                propertyName,
                generateWrapFieldNotPresentCondition(propertyToken.version(), indent),
                offset,
                fieldLength);
        }

        return sb;
    }

    private static void generateArrayLengthMethod(
        final String propertyName, final String indent, final int fieldLength, final StringBuilder sb)
    {
        final String formatPropertyName = formatPropertyName(propertyName);
        sb.append("\n")
            .append(indent).append("    @staticmethod\n")
            .append(indent).append("    def ").append(formatPropertyName).append("_length() -> int:\n")
            .append(indent).append("        return ").append(fieldLength).append("\n\n");
    }

    private CharSequence generatePrimitiveArrayPropertyEncode(
        final String containingClassName, final String propertyName, final Token token, final String indent)
    {
        final Encoding encoding = token.encoding();
        final PrimitiveType primitiveType = encoding.primitiveType();
        final String pythonTypeName = pythonTypeName(primitiveType);
        final int offset = token.offset();
        final String byteOrderStr = generateStructByteOrderCode(encoding.byteOrder());
        final int arrayLength = token.arrayLength();
        final int typeSize = sizeOfPrimitive(encoding);

        final StringBuilder sb = new StringBuilder();
        final String className = formatClassName(containingClassName);

        generateArrayLengthMethod(propertyName, indent, arrayLength, sb);

        new Formatter(sb).format("\n" +
            indent + "    def %s(self, index: int, value: %s) -> \"%s\":\n" +
            indent + "        if index < 0 or index >= %d:\n" +
            indent + "            raise IndexError(\"index out of range: index=\" + str(index))\n\n" +
            indent + "        pos: int = self._offset + %d + (index * %d)\n" +
            indent + "        %s\n\n" +
            indent + "        return self\n\n",
            propertyName,
            pythonTypeName,
            className,
            arrayLength,
            offset,
            typeSize,
            generatePut(primitiveType, "pos", "value", byteOrderStr));

        if (arrayLength > 1 && arrayLength <= 4)
        {
            sb.append(indent)
                .append("    def")
                .append(" put_").append(propertyName)
                .append("_values(self, value0: ").append(pythonTypeName);

            for (int i = 1; i < arrayLength; i++)
            {
                sb.append(", value").append(i).append(": ").append(pythonTypeName);
            }

            sb.append(") -> \"").append(className).append("\":\n");

            for (int i = 0; i < arrayLength; i++)
            {
                final String indexStr = "self._offset + " + (offset + (typeSize * i));

                sb.append(indent).append("        ")
                    .append(generatePut(primitiveType, indexStr, "value" + i, byteOrderStr))
                    .append("\n");
            }

            sb.append("\n");
            sb.append(indent).append("        return self\n");
        }

        if (primitiveType == PrimitiveType.CHAR)
        {
            generateCharArrayEncodeMethods(
                containingClassName, propertyName, indent, encoding, offset, arrayLength, sb);
        }
        else if (primitiveType == PrimitiveType.UINT8)
        {
            generateByteArrayEncodeMethods(
                containingClassName, propertyName, indent, offset, arrayLength, sb);
        }

        return sb;
    }

    private void generateCharArrayEncodeMethods(
        final String containingClassName,
        final String propertyName,
        final String indent,
        final Encoding encoding,
        final int offset,
        final int fieldLength,
        final StringBuilder sb)
    {
        generateCharacterEncodingMethod(sb, propertyName, encoding.characterEncoding(), indent);

        new Formatter(sb).format("\n" +
            indent + "    def put_%s(self, src: list[int], src_offset: int) -> \"%s\":\n" +
            indent + "        length: int = %d\n" +
            indent + "        if src_offset < 0 or src_offset > (len(src) - length):\n" +
            indent + "            raise IndexError(" +
            "\"Copy will go out of range: offset=\" + str(src_offset))\n\n" +
            indent + "        start = self._offset + %d\n" +
            indent + "        end = start + length\n" +
            indent + "        self.buffer()[start: end] = src[src_offset: src_offset + length]\n\n" +
            indent + "        return self\n",
            propertyName,
            formatClassName(containingClassName),
            fieldLength,
            offset);

        if (isAsciiEncoding(encoding.characterEncoding()))
        {
            new Formatter(sb).format("\n" +
                indent + "    def %1$s_string(self, src: str) -> \"%2$s\":\n" +
                indent + "        length: int = %3$d\n" +
                indent + "        encoded = src.encode(\"%5$s\") if src is not None else b\"\"\n" +
                indent + "        src_length = len(encoded)\n" +
                indent + "        if src_length > length:\n" +
                indent + "            raise IndexError(" +
                "\"String too large for copy: byte length=\" + str(src_length))\n\n" +
                indent + "        start = self._offset + %4$d\n" +
                indent + "        end = start + src_length\n" +
                indent + "        self.buffer()[start: end] = encoded\n\n" +
                indent + "        for i in range(src_length, length):\n" +
                indent + "            self.buffer()[start + i] = 0\n\n" +
                indent + "        return self\n",
                propertyName,
                formatClassName(containingClassName),
                fieldLength,
                offset,
                charset(encoding.characterEncoding()));
        }
        else
        {
            new Formatter(sb).format("\n" +
                indent + "    def %s_string(self, src: str) -> \"%s\":\n" +
                indent + "        length: int = %d\n" +
                indent + "        encoded = src.encode(\"%s\") if not src else b\"\"\n" +
                indent + "        if len(encoded) > length:\n" +
                indent + "            raise ValueError(f" +
                "\"String too large for copy: byte length={len(encoded)}\")\n\n" +
                indent + "        start =  self._offset + %d\n" +
                indent + "        end = start + len(encoded)\n" +
                indent + "        self.buffer()[start: end] = encoded\n\n" +
                indent + "        for i in range(len(encoded), length):\n" +
                indent + "            self.buffer()[start + i] = 0\n\n" +
                indent + "        return self\n",
                propertyName,
                formatClassName(containingClassName),
                fieldLength,
                charset(encoding.characterEncoding()),
                offset,
                offset);
        }
    }

    private void generateByteArrayEncodeMethods(
        final String containingClassName,
        final String propertyName,
        final String indent,
        final int offset,
        final int fieldLength,
        final StringBuilder sb)
    {
        new Formatter(sb).format("\n" +
            indent + "    def put_%s(self, src: list[int], src_offset: int, length: int) -> \"%s\":\n" +
            indent + "        if length > %d:\n" +
            indent + "            raise ValueError(" +
            "\"length > max_value for type: \" + str(length))\n\n" +
            indent + "        start = self._offset + %d\n" +
            indent + "        end = start + length\n" +
            indent + "        self.buffer()[start : end] = src[src_offset : src_offset + length]\n" +
            indent + "        for i  in range(length, %d):\n" +
            indent + "            self.buffer()[start + i] = 0\n\n" +
            indent + "        return self\n" +
            formatClassName(containingClassName),
            formatClassName(containingClassName),
            fieldLength,
            offset,
            fieldLength,
            offset);

        new Formatter(sb).format("\n" +
            indent + "    def put_%s(self, src: bytearray, src_offset: int, length: int) -> \"%s\":\n" +
            indent + "        if length > %d:\n" +
            indent + "            raise ValueError(" +
            "\"length > max_value for type: \" + str(length))\n\n" +
            indent + "        start = self._offset + %d\n" +
            indent + "        end = start + length\n" +
            indent + "        self.buffer()[start : end] = src[src_offset : src_offset + length]\n" +
            indent + "        for i in range(length, %d):\n" +
            indent + "            self.buffer()[start + i] = 0\n\n" +
            indent + "        return self\n",
            propertyName,
            formatClassName(containingClassName),
            fieldLength,
            offset,
            fieldLength,
            offset);
    }

    private static int sizeOfPrimitive(final Encoding encoding)
    {
        return encoding.primitiveType().size();
    }

    private static void generateCharacterEncodingMethod(
        final StringBuilder sb, final String propertyName, final String characterEncoding, final String indent)
    {
        if (null != characterEncoding)
        {
            final String propName = formatPropertyName(propertyName);
            sb.append("\n")
                .append(indent).append("    @staticmethod\n")
                .append(indent).append("    def ").append(propName).append("_character_encoding() -> str:\n")
                .append(indent).append("        return \"").append(charsetName(characterEncoding)).append("\"\n\n");
        }
    }

    private void generateConstPropertyMethods(
        final StringBuilder sb, final String className,
        final String propertyName, final Token token, final String indent)
    {
        final String formattedPropertyName = formatPropertyName(propertyName);
        final Encoding encoding = token.encoding();
        if (encoding.primitiveType() != PrimitiveType.CHAR)
        {
            new Formatter(sb).format("\n" +
                indent + "    def %s(self) -> %s:\n" +
                indent + "        return %s\n",
                formattedPropertyName,
                pythonTypeName(encoding.primitiveType()),
                generateLiteral(encoding.primitiveType(), encoding.constValue().toString()));

            return;
        }

        final byte[] constBytes = encoding.constValue().byteArrayValue(encoding.primitiveType());
        final CharSequence values = generateByteLiteralList(
            encoding.constValue().byteArrayValue(encoding.primitiveType()));

        new Formatter(sb).format("\n" +
            "\n" +
            indent + "    _%s_VALUE: list[int] = [ %s ]\n",
            propertyName.toUpperCase(),
            values);

        generateArrayLengthMethod(formattedPropertyName, indent, constBytes.length, sb);

        new Formatter(sb).format("\n" +
            indent + "    def %s(self, index: int) -> int:\n" +
            indent + "        return %s._%s_VALUE[index]\n\n",
            formattedPropertyName,
            className,
            propertyName.toUpperCase());

        sb.append(String.format(
            indent + "    def get_%s(self, dst, offset: int, length: int) -> int:\n" +
            indent + "        bytes_copied: int = min(length, %d)\n" +
            indent + "        dst.set(%s._%s_VALUE[0: bytes_copied], offset)\n\n" +
            indent + "        return bytes_copied\n\n",
            propertyName,
            constBytes.length,
            className,
            propertyName.toUpperCase()));

        if (constBytes.length > 1)
        {
            new Formatter(sb).format("\n" +
                indent + "    def %s_string(self) -> str:\n" +
                indent + "        return \"%s\"\n\n",
                formattedPropertyName,
                encoding.constValue());
        }
        else
        {
            new Formatter(sb).format("\n" +
                indent + "    def %s_value(self) -> int:\n" +
                indent + "        return %s\n\n",
                formattedPropertyName,
                encoding.constValue());
        }
    }

    private static CharSequence generateByteLiteralList(final byte[] bytes)
    {
        final StringBuilder values = new StringBuilder();
        for (final byte b : bytes)
        {
            values.append(b).append(", ");
        }

        if (!values.isEmpty())
        {
            values.setLength(values.length() - 2);
        }

        return values;
    }

    private CharSequence generateFixedFlyweightCode(final String className,
        final int size, final String constructorFields)
    {
        final String schemaIdType = pythonTypeName(ir.headerStructure().schemaIdType());
        final String schemaVersionType = pythonTypeName(ir.headerStructure().schemaVersionType());
        final String semanticVersion = ir.semanticVersion() == null ? "" : ir.semanticVersion();

        return String.format(
            """

            SCHEMA_ID: %1$s = %2$s
            SCHEMA_VERSION: %3$s = %4$s
            SEMANTIC_VERSION: str = "%5$s"
            ENCODED_LENGTH: int = %6$d
            BYTE_ORDER: str = "%7$s"

            def __init__(self):
                self._offset = 0
                self._buffer = None

        %9$s

            def wrap(self, buffer: bytes, offset: int):
                if buffer != self._buffer:
                    self._buffer = buffer
                self._offset = offset
                return self

            def buffer(self):
                if self._buffer is None:
                    raise ValueError("buffer is None")
                return self._buffer

            def offset(self):
                return self._offset

            def encoded_length(self):
                return %8$s.ENCODED_LENGTH

            def sbe_schema_id(self):
                return %8$s.SCHEMA_ID

            def sbe_schema_version(self):
                return %8$s.SCHEMA_VERSION

        """,
            schemaIdType,
            generateLiteral(ir.headerStructure().schemaIdType(), Integer.toString(ir.id())),
            schemaVersionType,
            generateLiteral(ir.headerStructure().schemaVersionType(), Integer.toString(ir.version())),
            semanticVersion,
            size,
            generateStructByteOrderCode(ir.byteOrder()),
            className,
            constructorFields);
    }

    private CharSequence generateDecoderFlyweightCode(final String className,
        final Token token, final String constructorFields)
    {
        final String headerClassName = formatClassName(ir.headerStructure().tokens().get(0).applicableTypeName());

        final String methods =
            "    def wrap(\n" +
            "        self,\n" +
            "        buffer: bytearray,\n" +
            "        offset: int,\n" +
            "        acting_block_length: int,\n" +
            "        acting_version: int) -> \"" + className + "\":\n" +
            "        if buffer != self._buffer:\n" +
            "            self._buffer = buffer\n\n" +
            "        self._initial_offset = offset\n" +
            "        self._offset = offset\n" +
            "        self._acting_block_length = acting_block_length\n" +
            "        self._acting_version = acting_version\n" +
            "        self.set_limit(offset + acting_block_length)\n\n" +
            "        return self\n\n" +

            "    def wrap_and_apply_header(\n" +
            "        self,\n" +
            "        buffer,\n" +
            "        offset: int,\n" +
            "        header_decoder: " + headerClassName + "Decoder) -> \"" + className + "\":\n\n" +
            "        header_decoder.wrap(buffer, offset)\n\n" +
            "        template_id: int = header_decoder.template_id()\n" +
            "        if " + className + ".TEMPLATE_ID != template_id:\n" +
            "            raise ValueError(\"Invalid TEMPLATE_ID: \" + str(template_id))\n\n" +
            "        return self.wrap(\n" +
            "            buffer,\n" +
            "            offset + " + headerClassName + "Decoder.ENCODED_LENGTH,\n" +
            "            header_decoder.block_length(),\n" +
            "            header_decoder.version())\n\n" +

            "    def sbe_rewind(self) -> \"" + className + "\":\n" +
            "        if self._buffer is None:\n" +
            "           raise ValueError(\"buffer is None\")\n" +
            "        return self.wrap(self._buffer, self._initial_offset,\n" +
            "            self._acting_block_length, self._acting_version)\n\n" +

            "    def sbe_decoded_length(self) -> int:\n" +
            "        current_limit: int = self.get_limit()\n" +
            "        self.sbe_skip()\n" +
            "        decoded_length: int = self.encoded_length()\n" +
            "        self.set_limit(current_limit)\n\n" +
            "        return decoded_length\n\n" +

            "    def acting_version(self) -> int:\n" +
            "        return self._acting_version\n\n";

        return generateFlyweightCode(DECODER, className, token, methods, constructorFields);
    }

    private CharSequence generateFlyweightCode(
        final CodecType codecType,
        final String className,
        final Token token,
        final String wrapMethod,
        final String constructorFields)
    {
        final HeaderStructure headerStructure = ir.headerStructure();
        final String blockLengthType = pythonTypeName(headerStructure.blockLengthType());
        final String blockLengthAccessorType = shouldGenerateInterfaces ? "int" : blockLengthType;
        final String templateIdType = pythonTypeName(headerStructure.templateIdType());
        final String templateIdAccessorType = shouldGenerateInterfaces ? "int" : templateIdType;
        final String schemaIdType = pythonTypeName(headerStructure.schemaIdType());
        final String schemaIdAccessorType = shouldGenerateInterfaces ? "int" : schemaIdType;
        final String schemaVersionType = pythonTypeName(headerStructure.schemaVersionType());
        final String schemaVersionAccessorType = shouldGenerateInterfaces ? "int" : schemaVersionType;
        final String semanticType = token.encoding().semanticType() == null ? "" : token.encoding().semanticType();
        final String semanticVersion = ir.semanticVersion() == null ? "" : ir.semanticVersion();
        final String actingFields = codecType == CodecType.ENCODER ?
            "" :
            """
                    self._acting_block_length: int = 0
                    self._acting_version: int = 0
            """;

        return String.format("""
            BLOCK_LENGTH: %1$s = %2$s
            TEMPLATE_ID: %3$s = %4$s
            SCHEMA_ID: %5$s = %6$s
            SCHEMA_VERSION: %7$s = %8$s
            SEMANTIC_VERSION: str = "%19$s"
            BYTE_ORDER: str = "%14$s"

            def __init__(self):
                self._parent_message: "%9$s" = self
                self._buffer: bytearray | None= None
                self._initial_offset: int = 0
                self._offset: int = 0
                self._limit: int = 0
        %13$s

        %20$s

            def sbe_block_length(self) -> %15$s:
                return %9$s.BLOCK_LENGTH

            def sbe_template_id(self) -> %16$s:
                return %9$s.TEMPLATE_ID

            def sbe_schema_id(self) -> %17$s:
                return %9$s.SCHEMA_ID

            def sbe_schema_version(self) -> %18$s:
                return %9$s.SCHEMA_VERSION

            def sbe_semantic_type(self) -> str:
                return "%10$s"

            def buffer(self) -> bytearray:
                if self._buffer is None:
                    raise ValueError("buffer is None")
                return self._buffer

            def initial_offset(self) -> int:
                return self._initial_offset

            def offset(self) -> int:
                return self._offset

        %12$s

            def encoded_length(self) -> int:
                return self._limit - self._offset

            def get_limit(self) -> int:
                return self._limit

            def set_limit(self, limit: int):
                self._limit = limit
        """,
            blockLengthType,
            generateLiteral(headerStructure.blockLengthType(), Integer.toString(token.encodedLength())),
            templateIdType,
            generateLiteral(headerStructure.templateIdType(), Integer.toString(token.id())),
            schemaIdType,
            generateLiteral(headerStructure.schemaIdType(), Integer.toString(ir.id())),
            schemaVersionType,
            generateLiteral(headerStructure.schemaVersionType(), Integer.toString(ir.version())),
            className,
            semanticType,
            "bytearray",
            wrapMethod,
            actingFields,
            generateStructByteOrderCode(ir.byteOrder()),
            blockLengthAccessorType,
            templateIdAccessorType,
            schemaIdAccessorType,
            schemaVersionAccessorType,
            semanticVersion,
            constructorFields);
    }

    private CharSequence generateEncoderFlyweightCode(final String className,
        final Token token, final String constructorFields)
    {
        final String wrapMethod =
            "    def wrap(self, buffer, offset: int) -> \"" + className + "\":\n" +
            "        if buffer != self._buffer:\n" +
            "            self._buffer = buffer\n\n" +
            "        self._initial_offset = offset\n" +
            "        self._offset = offset\n" +
            "        self.set_limit(offset + " + className + ".BLOCK_LENGTH)\n\n" +
            "        return self\n\n";

        final StringBuilder builder = new StringBuilder(
            """
                def wrap_and_apply_header(
                    self,
                    buffer: bytearray, offset: int, header_encoder: %2$s) -> "%1$s":
                    header_encoder.wrap(buffer, offset)%3$s
            """);

        final StringBuilder headerBuilder = new StringBuilder();

        for (final Token headerToken : ir.headerStructure().tokens())
        {
            if (!headerToken.isConstantEncoding())
            {
                switch (headerToken.name())
                {
                    case "block_length":
                        headerBuilder.append(".block_length(").append(className).append(".BLOCK_LENGTH)");
                        break;

                    case "template_id":
                        headerBuilder.append(".template_id(").append(className).append(".TEMPLATE_ID)");
                        break;

                    case "schema_id":
                        headerBuilder.append(".schema_id(").append(className).append(".SCHEMA_ID)");
                        break;

                    case "version":
                        headerBuilder.append(".version(").append(className).append(".SCHEMA_VERSION)");
                        break;
                }
            }
        }

        builder.append("\n\n        return self.wrap(buffer, offset + %2$s.ENCODED_LENGTH)\n\n");

        final String wrapAndApplyMethod = String.format(
            builder.toString(),
            className,
            formatClassName(ir.headerStructure().tokens().get(0).applicableTypeName() + "Encoder"),
            headerBuilder.toString());

        return generateFlyweightCode(
            CodecType.ENCODER, className, token, wrapMethod + wrapAndApplyMethod, constructorFields);
    }

    private void generateEncoderFields(
        final StringBuilder sb, final String containingClassName, final List<Token> tokens, final String indent)
    {
        Generators.forEachField(
            tokens,
            (fieldToken, typeToken) ->
            {
                final String propertyName = formatPropertyName(fieldToken.name());
                final String typeName = encoderName(typeToken.name());

                generateFieldIdMethod(sb, fieldToken, indent);
                generateFieldSinceVersionMethod(sb, fieldToken, indent);
                generateEncodingOffsetMethod(sb, propertyName, fieldToken.offset(), indent);
                generateEncodingLengthMethod(sb, propertyName, typeToken.encodedLength(), indent);
                generateFieldMetaAttributeMethod(sb, fieldToken, indent);

                switch (typeToken.signal())
                {
                    case ENCODING:
                        generatePrimitiveEncoder(sb, containingClassName, propertyName, typeToken, indent);
                        break;

                    case BEGIN_ENUM:
                        generateEnumEncoder(sb, containingClassName, fieldToken, propertyName, typeToken, indent);
                        break;

                    case BEGIN_SET:
                        generateBitSetProperty(
                            sb, false, ENCODER, propertyName, fieldToken, typeToken, indent, typeName);
                        break;

                    case BEGIN_COMPOSITE:
                        generateCompositeProperty(
                            sb, false, ENCODER, propertyName, fieldToken, typeToken, indent, typeName);
                        break;

                    default:
                        break;
                }
            });
    }

    private void generateDecoderFields(final StringBuilder sb, final String containingClassName,
        final List<Token> tokens, final String indent)
    {
        Generators.forEachField(
            tokens,
            (fieldToken, typeToken) ->
            {
                final String propertyName = formatPropertyName(fieldToken.name());
                final String typeName = decoderName(typeToken.name());

                generateFieldIdMethod(sb, fieldToken, indent);
                generateFieldSinceVersionMethod(sb, fieldToken, indent);
                generateEncodingOffsetMethod(sb, propertyName, fieldToken.offset(), indent);
                generateEncodingLengthMethod(sb, propertyName, typeToken.encodedLength(), indent);
                generateFieldMetaAttributeMethod(sb, fieldToken, indent);

                switch (typeToken.signal())
                {
                    case ENCODING:
                        generatePrimitiveDecoder(sb, false, propertyName, fieldToken, typeToken, indent,
                            containingClassName);
                        break;

                    case BEGIN_ENUM:
                        generateEnumDecoder(sb, false, fieldToken, propertyName, typeToken, indent);
                        break;

                    case BEGIN_SET:
                        generateBitSetProperty(
                            sb, false, DECODER, propertyName, fieldToken, typeToken, indent, typeName);
                        break;

                    case BEGIN_COMPOSITE:
                        generateCompositeProperty(
                            sb, false, DECODER, propertyName, fieldToken, typeToken, indent, typeName);
                        break;

                    default:
                        break;
                }
            });
    }

    private static void generateFieldIdMethod(final StringBuilder sb, final Token token, final String indent)
    {
        final String propertyName = formatPropertyName(token.name());
        sb.append("\n")
            .append(indent).append("    @staticmethod\n")
            .append(indent).append("    def ").append(propertyName).append("_id() -> int:\n")
            .append(indent).append("        return ").append(token.id()).append("\n");
    }

    private static void generateEncodingOffsetMethod(
        final StringBuilder sb, final String name, final int offset, final String indent)
    {
        final String propertyName = formatPropertyName(name);
        sb.append("\n")
            .append(indent).append("    @staticmethod\n")
            .append(indent).append("    def ").append(propertyName).append("_encoding_offset() -> int :\n")
            .append(indent).append("        return ").append(offset).append("\n");
    }

    private static void generateEncodingLengthMethod(
        final StringBuilder sb, final String name, final int length, final String indent)
    {
        final String propertyName = formatPropertyName(name);
        sb.append("\n")
            .append(indent).append("    @staticmethod\n")
            .append(indent).append("    def ").append(propertyName).append("_encoding_length() -> int:\n")
            .append(indent).append("        return ").append(length).append("\n");
    }

    private static void generateFieldSinceVersionMethod(final StringBuilder sb, final Token token, final String indent)
    {
        final String propertyName = formatPropertyName(token.name());
        sb.append("\n")
            .append(indent).append("    @staticmethod\n")
            .append(indent).append("    def ").append(propertyName).append("_since_version() -> int:\n")
            .append(indent).append("        return ").append(token.version()).append("\n");
    }

    private static void generateFieldMetaAttributeMethod(final StringBuilder sb, final Token token, final String indent)
    {
        final Encoding encoding = token.encoding();
        final String epoch = encoding.epoch() == null ? "" : encoding.epoch();
        final String timeUnit = encoding.timeUnit() == null ? "" : encoding.timeUnit();
        final String semanticType = encoding.semanticType() == null ? "" : encoding.semanticType();
        final String presence = encoding.presence().toString().toLowerCase();
        final String propertyName = formatPropertyName(token.name());

        sb.append("\n")
            .append(indent).append("    @staticmethod\n")
            .append(indent).append("    def ")
            .append(propertyName).append("_meta_attribute(meta_attribute: MetaAttribute) -> str:\n")
            .append(indent).append("        if MetaAttribute.PRESENCE == meta_attribute:\n")
            .append(indent).append("            return \"").append(presence).append("\"\n\n");

        if (!Strings.isEmpty(epoch))
        {
            sb.append(indent).append("        if MetaAttribute.EPOCH == meta_attribute:\n")
                .append(indent).append("            return \"").append(epoch).append("\"\n\n");
        }

        if (!Strings.isEmpty(timeUnit))
        {
            sb.append(indent).append("        if MetaAttribute.TIME_UNIT == meta_attribute:\n")
                .append(indent).append("            return \"").append(timeUnit).append("\"\n\n");
        }

        if (!Strings.isEmpty(semanticType))
        {
            sb.append(indent).append("        if MetaAttribute.SEMANTIC_TYPE == meta_attribute:\n")
                .append(indent).append("            return \"").append(semanticType).append("\"\n\n");
        }

        sb.append(indent).append("        return \"\"\n\n");
    }

    private void generateEnumDecoder(
        final StringBuilder sb,
        final boolean inComposite,
        final Token fieldToken,
        final String propertyName,
        final Token typeToken,
        final String indent)
    {
        final String enumName = formatClassName(typeToken.applicableTypeName());
        final Encoding encoding = typeToken.encoding();
        final String pythonTypeName = pythonTypeName(encoding.primitiveType());

        if (fieldToken.isConstantEncoding())
        {
            final String enumValueStr = fieldToken.encoding().constValue().toString();

            new Formatter(sb).format(
                "\n" +
                indent + "    def %s_raw(self) -> %s:\n" +
                indent + "        return %s\n\n",
                propertyName,
                pythonTypeName,
                enumValueStr);

            new Formatter(sb).format(
                "\n" +
                indent + "    def %s(self) -> %s:\n" +
                indent + "        return %s\n\n",
                propertyName,
                enumName,
                enumValueStr);
        }
        else
        {
            final String rawGetStr = generateGet(
                encoding.primitiveType(), "self._offset + " + typeToken.offset(),
                generateStructByteOrderCode(encoding.byteOrder()));

            CharSequence noPresentCondition = generateFieldNotPresentCondition(inComposite,
                fieldToken.version(), encoding, indent);

            new Formatter(sb).format(
                "\n" +
                indent + "    def %s_raw(self) -> %s:\n" +
                "%s" +
                indent + "        return %s\n\n",
                formatPropertyName(propertyName),
                noPresentCondition.isEmpty() ? pythonTypeName : pythonTypeName + " | None",
                noPresentCondition,
                rawGetStr);

            noPresentCondition = generatePropertyNotPresentCondition(inComposite, DECODER,
                fieldToken, enumName, indent);

            new Formatter(sb).format(
                "\n" +
                indent + "    def %s(self) -> %s:\n" +
                "%s" +
                indent + "        enum_value: int = %s\n" +
                indent + "        return %s.get(enum_value)\n\n",
                propertyName,
                noPresentCondition.isEmpty() ? enumName : enumName + " | None",
                noPresentCondition,
                rawGetStr,
                enumName);
        }
    }

    private void generateEnumEncoder(
        final StringBuilder sb,
        final String containingClassName,
        final Token fieldToken,
        final String propertyName,
        final Token typeToken,
        final String indent)
    {
        if (!fieldToken.isConstantEncoding())
        {
            final String enumName = formatClassName(typeToken.applicableTypeName());
            final Encoding encoding = typeToken.encoding();
            final int offset = typeToken.offset();
            final String byteOrderString = generateStructByteOrderCode(encoding.byteOrder());

            new Formatter(sb).format("\n" +
                indent + "    def %s(self, value: %s) -> \"%s\":\n" +
                indent + "        %s\n" +
                indent + "        return self\n\n",
                propertyName,
                enumName,
                formatClassName(containingClassName),
                generatePut(encoding.primitiveType(), "self._offset + " + offset, "value", byteOrderString));
        }
    }

    private void generateBitSetProperty(
        final StringBuilder sb,
        final boolean inComposite,
        final CodecType codecType,
        final String propertyName,
        final Token propertyToken,
        final Token bitsetToken,
        final String indent,
        final String bitSetName)
    {

        generateFlyweightPropertyReStructuredText(sb, indent + INDENT, propertyToken, bitSetName);

        final CharSequence notPresentCondition = generatePropertyNotPresentCondition(
            inComposite, codecType, propertyToken, null, indent);

        new Formatter(sb).format("\n" +
            indent + "    def %s(self) -> %s:\n" +
            "%s" +
            indent + "        self._%s.wrap(self._buffer, self._offset + %d)\n" +
            indent + "        return self._%s\n\n",
            propertyName,
            notPresentCondition.isEmpty() ? bitSetName : bitSetName + " | None",
            notPresentCondition,
            propertyName,
            bitsetToken.offset(),
            propertyName);
    }

    private void generateCompositeProperty(
        final StringBuilder sb,
        final boolean inComposite,
        final CodecType codecType,
        final String propertyName,
        final Token propertyToken,
        final Token compositeToken,
        final String indent,
        final String compositeName)
    {

        generateFlyweightPropertyReStructuredText(sb, indent + INDENT, propertyToken, compositeName);

        final CharSequence notPresentCondition = generatePropertyNotPresentCondition(
            inComposite, codecType, propertyToken, null, indent);

        new Formatter(sb).format("\n" +
            indent + "    def %s(self) -> %s:\n" +
            "%s" +
            indent + "        self._%s.wrap(self._buffer, self._offset + %d)\n" +
            indent + "        return self._%s\n\n",
            propertyName,
            notPresentCondition.isEmpty() ? compositeName : compositeName + " | None",
            notPresentCondition,
            propertyName,
            compositeToken.offset(),
            propertyName);
    }

    private String generateCoderImports(final String className, final CodecType codecType,
        final List<Token> fields, final List<Token> groups)
    {

        final StringBuilder sb = new StringBuilder();
        final Set<String> imports = new HashSet<>();

        scanForImports(imports, fields, codecType);

        scanGroupsForImports(imports, groups, codecType);

        for (final String importName : imports)
        {
            sb.append(String.format(
                """
                from .%1$s import %1$s
                """,
                importName));
        }

        if (codecType == ENCODER)
        {
            sb.append(String.format("from .%1$s import %1$s\n", decoderName(className)));
        }

        sb.append(String.format("""
            from .MessageHeader%1$s import MessageHeader%1$s
            from .MetaAttribute import MetaAttribute
            """, codecType == ENCODER ? "Encoder" : "Decoder"));

        return sb.toString();
    }

    private String generateCompositeImports(final String className,
        final CodecType codecType, final List<Token> fields)
    {

        final StringBuilder sb = new StringBuilder();
        final Set<String> imports = new HashSet<>();

        scanForImports(imports, fields, codecType);

        for (final String importName : imports)
        {
            sb.append(String.format("""
                from .%1$s import %1$s
                """,
                importName));
        }

        if (codecType == ENCODER)
        {
            sb.append(String.format("from .%1$s import %1$s ", decoderName(className)));
        }

        return sb.toString();
    }

    private void scanGroupsForImports(final Set<String> imports, final List<Token> groups, final CodecType codecType)
    {

        for (int i = 0, end = groups.size() - 1; i < end;)
        {

            final Token groupToken = groups.get(i);

            ++i;
            final int groupHeaderTokenCount = groups.get(i).componentTokenCount();
            i += groupHeaderTokenCount;

            final List<Token> fields = new ArrayList<>();
            i = collectFields(groups, i, fields);

            final List<Token> subGroups = new ArrayList<>();
            i = collectGroups(groups, i, subGroups);

            scanForImports(imports, fields, codecType);

            scanGroupsForImports(imports, subGroups, codecType);

            ++i;
        }
    }

    private void scanForImports(final Set<String> imports, final List<Token> tokens, final CodecType codecType)
    {

        for (int i = 0, size = tokens.size(); i < size;)
        {
            final Token fieldToken = tokens.get(i);
            if (fieldToken.signal() == Signal.BEGIN_FIELD)
            {
                final Token typeToken = tokens.get(i + 1);
                if (typeToken.signal() == Signal.BEGIN_COMPOSITE || typeToken.signal() == Signal.BEGIN_SET)
                {
                    final String coderName = codecType == DECODER ?
                        decoderName(typeToken.applicableTypeName()) : encoderName(typeToken.applicableTypeName());
                    imports.add(coderName);
                }
                else if (typeToken.signal() == Signal.BEGIN_ENUM)
                {
                    imports.add(typeToken.applicableTypeName());
                }
            }
            else if (fieldToken.signal() == Signal.BEGIN_COMPOSITE || fieldToken.signal() == Signal.BEGIN_SET)
            {
                final String coderName = codecType == DECODER ?
                    decoderName(fieldToken.applicableTypeName()) : encoderName(fieldToken.applicableTypeName());
                imports.add(coderName);
            }
            else if (fieldToken.signal() == Signal.BEGIN_ENUM)
            {
                imports.add(fieldToken.applicableTypeName());
            }

            i += fieldToken.componentTokenCount();
        }
    }

    private String generateConstructorFields(final List<Token> fields,
        final List<Token> groups, final CodecType codecType)
    {

        final StringBuilder sb = new StringBuilder();

        for (int i = 0, size = fields.size(); i < size;)
        {
            final Token fieldToken = fields.get(i);
            final String propertyName = formatPropertyName(fieldToken.name());
            final String typeName;
            if (fieldToken.signal() == Signal.BEGIN_FIELD)
            {
                final Token typeToken = fields.get(i + 1);
                if (typeToken.signal() == Signal.BEGIN_COMPOSITE || typeToken.signal() == Signal.BEGIN_SET)
                {
                    typeName = codecType == ENCODER ?
                        encoderName(typeToken.applicableTypeName()) : decoderName(typeToken.applicableTypeName());
                    sb.append(String.format("""
                                self._%1$s: %2$s = %2$s()
                        """,
                        propertyName,
                        typeName));
                }
            }
            else if (fieldToken.signal() == Signal.BEGIN_COMPOSITE || fieldToken.signal() == Signal.BEGIN_SET)
            {
                typeName = codecType == ENCODER ?
                    encoderName(fieldToken.applicableTypeName()) : decoderName(fieldToken.applicableTypeName());
                sb.append(String.format("""
                            self._%1$s: %2$s = %2$s()
                    """,
                    propertyName,
                    typeName));
            }

            i += fieldToken.componentTokenCount();
        }

        sb.append("\n");

        for (int i = 0, end = groups.size() - 1; i < end;)
        {
            final Token encodingToken = groups.get(i);

            final String propertyName = formatPropertyName(encodingToken.name());
            final String typeName = codecType == ENCODER ?
                encoderName(encodingToken.applicableTypeName()) : decoderName(encodingToken.applicableTypeName());

            if (encodingToken.signal() == Signal.BEGIN_GROUP)
            {

                sb.append(String.format("""
                            self._%1$s: %2$s = %2$s(self)
                    """,
                    propertyName,
                    typeName));
            }
            i += encodingToken.componentTokenCount();
        }

        return sb.toString();

    }

    private String generateGet(final PrimitiveType type, final String index, final String byteOrder)
    {
        return String.format(
            "struct.unpack_from(\"%1$s%2$s\", self._buffer, %3$s)[0]%4$s",
            byteOrder,
            generateStructFormatCode(type),
            index,
            type == PrimitiveType.CHAR ? ".decode()" : "");
    }

    private String generatePut(
        final PrimitiveType type, final String index, final String value, final String byteOrder)
    {
        return String.format(
            "struct.pack_into(\"%1$s%2$s\", self._buffer, %3$s, %4$s%5$s)",
            byteOrder,
            generateStructFormatCode(type),
            index,
            value,
            type == PrimitiveType.CHAR ? "[0:1]" : "");
    }

    private String generateChoiceIsEmpty(final PrimitiveType type)
    {
        return String.format("""

                def is_empty(self) -> bool:
                    return 0 == struct.unpack_from("<%s", self._buffer, self._offset)
            """, generateStructFormatCode(type));
    }

    private String generateChoiceGet(final PrimitiveType type, final String bitIndex, final String byteOrder)
    {
        return String.format(
            "0 != (struct.unpack_from(\"%1$s%2$s\", self._buffer, self._offset)[0] & (1 << %3$s))",
            generateStructFormatCode(type),
            byteOrder,
            bitIndex
            );

    }

    private String generateStaticChoiceGet(final String bitIndex)
    {
        return String.format("value & (1 << %s) != 0", bitIndex);
    }

    private String generateChoicePut(final PrimitiveType type, final String bitIdx, final String byteOrder)
    {
        return String.format("""
                    bits: int = struct.unpack_from("%1$s%2$s", self._buffer, self._offset)[0]
                    bits = bits | (1 << %3$s) if value else bits & ~(1 << %3$s)
                    struct.pack_into("%1$s%2$s", self._buffer, self._offset, bits)
            """, byteOrder, generateStructFormatCode(type), bitIdx);
    }

    private String generateStaticChoicePut(final PrimitiveType type, final String bitIdx)
    {
        return String.format("""
                    return bits | (1 << %1$s) if value else bits & ~(1 << %1$s)
            """, bitIdx);
    }

    private void generateEncoderDisplay(final StringBuilder sb, final String decoderName)
    {
        appendToString(sb);

        sb.append('\n');
        append(sb, INDENT, "def append_to(self, string_to_append: list[str]) -> list[str]:");
        append(sb, INDENT, "    if self._buffer is None:");
        append(sb, INDENT, "        return string_to_append\n");
        append(sb, INDENT, "    decoder: " + decoderName + " = " + decoderName + "()");
        append(sb, INDENT, "    decoder.wrap(self._buffer, self._initial_offset, ");
        append(sb, INDENT, "        " + decoderName + ".BLOCK_LENGTH, ");
        append(sb, INDENT, "        " + decoderName + ".SCHEMA_VERSION)");
        sb.append('\n');
        append(sb, INDENT, "    return decoder.append_to(string_to_append)");
    }

    private CharSequence generateCompositeEncoderDisplay(final String decoderName)
    {
        final StringBuilder sb = new StringBuilder();

        appendToString(sb);
        sb.append('\n');
        append(sb, INDENT, "def append_to(self, string_to_append: list[str]) -> list[str]:");
        append(sb, INDENT, "    if self._buffer is None:");
        append(sb, INDENT, "        return string_to_append");
        sb.append('\n');
        append(sb, INDENT, "    decoder: " + decoderName + " = " + decoderName + "()");
        append(sb, INDENT, "    decoder.wrap(self._buffer, self._offset)");
        sb.append('\n');
        append(sb, INDENT, "    return decoder.append_to(string_to_append)");

        return sb;
    }

    private CharSequence generateCompositeDecoderDisplay(
        final List<Token> tokens,
        final String className)
    {
        final StringBuilder sb = new StringBuilder();

        appendToString(sb);
        sb.append('\n');
        append(sb, INDENT, "def append_to(self, string_to_append: list[str]) -> list[str]:");
        append(sb, INDENT, "    if self._buffer is None:");
        append(sb, INDENT, "        return string_to_append");
        sb.append('\n');
        Separator.BEGIN_COMPOSITE.appendToGeneratedBuilder(sb, INDENT + INDENT);

        int lengthBeforeLastGeneratedSeparator = -1;

        for (int i = 1, end = tokens.size() - 1; i < end;)
        {
            final Token encodingToken = tokens.get(i);
            final String propertyName = formatPropertyName(encodingToken.name());
            lengthBeforeLastGeneratedSeparator =
                writeTokenDisplay(propertyName, encodingToken, sb, INDENT + INDENT, className);
            i += encodingToken.componentTokenCount();
        }

        if (-1 != lengthBeforeLastGeneratedSeparator)
        {
            sb.setLength(lengthBeforeLastGeneratedSeparator);
        }

        Separator.END_COMPOSITE.appendToGeneratedBuilder(sb, INDENT + INDENT);
        sb.append('\n');
        append(sb, INDENT, "    return string_to_append");

        return sb;
    }

    private CharSequence generateChoiceDisplay(final List<Token> tokens)
    {
        final StringBuilder sb = new StringBuilder();

        appendToString(sb);
        sb.append('\n');
        append(sb, INDENT, "def append_to(self, string_to_append: list[str]) -> list[str]:");
        Separator.BEGIN_SET.appendToGeneratedBuilder(sb, INDENT + INDENT);
        append(sb, INDENT, "    at_least_one: bool = False");

        for (final Token token : tokens)
        {
            if (token.signal() == Signal.CHOICE)
            {
                final String choiceName = formatPropertyName(token.name());
                append(sb, INDENT, "    if self." + choiceName + "():");
                append(sb, INDENT, "        if at_least_one:");
                Separator.ENTRY.appendToGeneratedBuilder(sb, INDENT + INDENT + INDENT + INDENT);
                append(sb, INDENT, "        string_to_append.append( \"" + choiceName + "\")");
                append(sb, INDENT, "        at_least_one = True");
            }
        }

        Separator.END_SET.appendToGeneratedBuilder(sb, INDENT + INDENT);
        sb.append('\n');
        append(sb, INDENT, "    return string_to_append");

        return sb;
    }

    private void generateDecoderDisplay(
        final StringBuilder sb,
        final String name,
        final List<Token> tokens,
        final List<Token> groups,
        final List<Token> varData)
    {
        final String decoderName = decoderName(name);
        appendMessageToString(sb, decoderName(name));
        sb.append('\n');
        append(sb, INDENT, "def append_to(self, string_to_append: list[str]) -> list[str]:");
        append(sb, INDENT, "    if self._buffer is None:");
        append(sb, INDENT, "        return string_to_append");
        sb.append('\n');
        append(sb, INDENT, "    original_limit: int = self.get_limit()");
        append(sb, INDENT, "    self.set_limit(self._initial_offset + self._acting_block_length)");
        append(sb, INDENT, "    string_to_append.append(\"[" + name + "](sbe_template_id=\")");
        append(sb, INDENT, "    string_to_append.append(str(" + decoderName + ".TEMPLATE_ID))");
        append(sb, INDENT, "    string_to_append.append(\"|sbe_schema_id=\")");
        append(sb, INDENT, "    string_to_append.append(str(" + decoderName + ".SCHEMA_ID))");
        append(sb, INDENT, "    string_to_append.append(\"|sbe_schema_version=\")");
        append(sb, INDENT, "    if self._parent_message.acting_version() != " + decoderName + ".SCHEMA_VERSION:");
        append(sb, INDENT, "        string_to_append.append(str(self._parent_message.acting_version()))");
        append(sb, INDENT, "        string_to_append.append('/')");
        append(sb, INDENT, "    string_to_append.append(str(" + decoderName + ".SCHEMA_VERSION))");
        append(sb, INDENT, "    string_to_append.append(\"|sbe_block_length=\")");
        append(sb, INDENT, "    if self._acting_block_length != " + decoderName + ".BLOCK_LENGTH:");
        append(sb, INDENT, "        string_to_append.append(str(self._acting_block_length))");
        append(sb, INDENT, "        string_to_append.append('/')");
        append(sb, INDENT, "    string_to_append.append(str(" + decoderName + ".BLOCK_LENGTH))");
        append(sb, INDENT, "    string_to_append.append(\"):\")");
        appendDecoderDisplay(sb, tokens, groups, varData, INDENT + INDENT, decoderName);
        sb.append('\n');
        append(sb, INDENT, "    self.set_limit(original_limit)");
        sb.append('\n');
        append(sb, INDENT, "    return string_to_append");
    }

    private void appendGroupInstanceDecoderDisplay(
        final StringBuilder sb,
        final List<Token> fields,
        final List<Token> groups,
        final List<Token> varData,
        final String baseIndent,
        final String decoderName)
    {
        final String indent = baseIndent + INDENT;

        sb.append('\n');
        append(sb, indent, "def append_to(self, string_to_append: list[str]) -> list[str]:");
        append(sb, indent, "    if self._buffer is None:");
        append(sb, indent, "        return string_to_append");
        sb.append('\n');
        Separator.BEGIN_COMPOSITE.appendToGeneratedBuilder(sb, indent + INDENT);
        appendDecoderDisplay(sb, fields, groups, varData, indent + INDENT, decoderName);
        Separator.END_COMPOSITE.appendToGeneratedBuilder(sb, indent + INDENT);
        sb.append('\n');
        append(sb, indent, "    return string_to_append");
    }

    private void appendDecoderDisplay(
        final StringBuilder sb,
        final List<Token> fields,
        final List<Token> groups,
        final List<Token> varData,
        final String indent,
        final String className)
    {
        int lengthBeforeLastGeneratedSeparator = -1;

        for (int i = 0, size = fields.size(); i < size;)
        {
            final Token fieldToken = fields.get(i);
            if (fieldToken.signal() == Signal.BEGIN_FIELD)
            {
                final Token encodingToken = fields.get(i + 1);
                final String fieldName = formatPropertyName(fieldToken.name());
                lengthBeforeLastGeneratedSeparator = writeTokenDisplay(fieldName, encodingToken, sb, indent, className);

                i += fieldToken.componentTokenCount();
            }
            else
            {
                ++i;
            }
        }

        for (int i = 0, size = groups.size(); i < size; i++)
        {
            final Token groupToken = groups.get(i);
            if (groupToken.signal() != Signal.BEGIN_GROUP)
            {
                throw new IllegalStateException("tokens must begin with BEGIN_GROUP: token=" + groupToken);
            }

            final String groupName = formatPropertyName(groupToken.name());
            final String groupDecoderName = decoderName(groupToken.name());

            append(
                sb, indent, "string_to_append.append(\"" + groupName +
                Separator.KEY_VALUE + Separator.BEGIN_GROUP + "\")");
            append(sb, indent, groupName + ":" + groupDecoderName + " = self." + groupName + "()");
            append(sb, indent, groupName + "_original_offset: int = " + groupName + ".get_offset()");
            append(sb, indent, groupName + "_original_index: int = " + groupName + ".get_index()");

            append(sb, indent, "if " + groupName + ".count() > 0:");
            append(sb, indent, "    for _ in " + groupName + ":");
            append(sb, indent, "        " + groupName + ".append_to(string_to_append)");
            Separator.ENTRY.appendToGeneratedBuilder(sb, indent);

            append(sb, indent, groupName + ".set_offset(" + groupName + "_original_offset)");
            append(sb, indent, groupName + ".set_index(" + groupName + "_original_index)");
            Separator.END_GROUP.appendToGeneratedBuilder(sb, indent);


            lengthBeforeLastGeneratedSeparator = sb.length();
            Separator.FIELD.appendToGeneratedBuilder(sb, indent);

            i = findEndSignal(groups, i, Signal.END_GROUP, groupToken.name());
        }

        for (int i = 0, size = varData.size(); i < size;)
        {
            final Token varDataToken = varData.get(i);
            if (varDataToken.signal() != Signal.BEGIN_VAR_DATA)
            {
                throw new IllegalStateException("tokens must begin with BEGIN_VAR_DATA: token=" + varDataToken);
            }

            final String characterEncoding = varData.get(i + 3).encoding().characterEncoding();
            final String varDataName = formatPropertyName(varDataToken.name());
            append(sb, indent, "string_to_append.append(\"" + varDataName + Separator.KEY_VALUE + "\")");
            if (null == characterEncoding)
            {
                final String name = Generators.toUpperFirstChar(varDataToken.name());
                append(sb, indent, "string_to_append.append(skip" + name + "() + \" bytes of raw data\")");
            }
            else
            {
                if (isAsciiEncoding(characterEncoding))
                {
                    append(sb, indent, "string_to_append.append('\\'')");
                    append(sb, indent, "string_to_append.append('\\'')");
                }
                else
                {
                    append(sb, indent, "string_to_append.append('\\'' + self." + varDataName + "() + '\\'')");
                }
            }

            lengthBeforeLastGeneratedSeparator = sb.length();
            Separator.FIELD.appendToGeneratedBuilder(sb, indent);

            i += varDataToken.componentTokenCount();
        }

        if (-1 != lengthBeforeLastGeneratedSeparator)
        {
            sb.setLength(lengthBeforeLastGeneratedSeparator);
        }
    }

    private int writeTokenDisplay(
        final String fieldName,
        final Token typeToken,
        final StringBuilder sb,
        final String indent,
        final String className)
    {
        if (typeToken.encodedLength() <= 0 || typeToken.isConstantEncoding())
        {
            return -1;
        }

        append(sb, indent, "string_to_append.append(\"" + fieldName + Separator.KEY_VALUE + "\")");

        switch (typeToken.signal())
        {
            case ENCODING:
                if (typeToken.arrayLength() > 1)
                {
                    if (typeToken.encoding().primitiveType() == PrimitiveType.CHAR)
                    {
                        append(sb, indent, "i = 0");
                        append(sb, indent,
                            "while i < " + className + "." + fieldName + "_length() " +
                            "and int(self." + fieldName + "(i)) > 0:");
                        append(sb, indent, "    i+=1");
                        append(sb, indent, "    string_to_append.append(str(self." + fieldName + "(i)))");
                    }
                    else
                    {
                        Separator.BEGIN_ARRAY.appendToGeneratedBuilder(sb, indent);
                        append(sb, indent, "if " + className + "." + fieldName + "_length() > 0:");
                        append(sb, indent, "    for i in range(" + className + "." + fieldName + "_length()):");
                        append(sb, indent, "        string_to_append.append(str(self." + fieldName + "(i)))");
                        Separator.ENTRY.appendToGeneratedBuilder(sb, indent);
                        Separator.END_ARRAY.appendToGeneratedBuilder(sb, indent);
                    }
                }
                else
                {
                    // have to duplicate because of checkstyle :/
                    append(sb, indent, "string_to_append.append(str(self." + fieldName + "()))");
                }
                break;

            case BEGIN_ENUM:
                append(sb, indent, "string_to_append.append(str(self." + fieldName + "()))");
                break;

            case BEGIN_SET:
                append(sb, indent, "field = self." + fieldName + "()");
                append(sb, indent, "field.append_to(string_to_append) if field is not None else None");
                break;

            case BEGIN_COMPOSITE:
            {
                final String typeName = formatClassName(decoderName(typeToken.applicableTypeName()));
                append(sb, indent, fieldName + ": " + typeName + " = self." + fieldName + "()");
                append(sb, indent, "if " + fieldName + " is not None:");
                append(sb, indent, "    " + fieldName + ".append_to(string_to_append)");
                append(sb, indent, "else:");
                append(sb, indent, "    string_to_append.append(\"None\")");
                break;
            }

            default:
                break;
        }

        final int lengthBeforeFieldSeparator = sb.length();
        Separator.FIELD.appendToGeneratedBuilder(sb, indent);

        return lengthBeforeFieldSeparator;
    }

    private void appendToString(final StringBuilder sb)
    {
        sb.append('\n');
        append(sb, INDENT, "def __str__(self):");
        append(sb, INDENT, "    if self._buffer is None:");
        append(sb, INDENT, "        return \"\"\n");
        append(sb, INDENT, "    return \" \".join(self.append_to([]))");
    }

    private void appendMessageToString(final StringBuilder sb, final String decoderName)
    {
        sb.append('\n');
        append(sb, INDENT, "def __str__(self):");
        append(sb, INDENT, "    if self._buffer is None:");
        append(sb, INDENT, "        return \"\"\n");
        append(sb, INDENT, "    decoder: " + decoderName +
            " = " + decoderName + "()");
        append(sb, INDENT, "    decoder.wrap(self._buffer, self._initial_offset, ");
        append(sb, INDENT, "        self._acting_block_length, self._acting_version)");
        sb.append('\n');
        append(sb, INDENT, "    return \" \".join(decoder.append_to([]))");
    }

    private void generateMessageLength(
        final StringBuilder sb,
        final String className,
        final boolean isParent,
        final List<Token> groups,
        final List<Token> varData,
        final String baseIndent)
    {
        final String methodIndent = baseIndent + INDENT;
        final String bodyIndent = methodIndent + INDENT;

        append(sb, methodIndent, "");
        append(sb, methodIndent, "def sbe_skip(self) -> \"" + className + "\":");

        if (isParent)
        {
            append(sb, bodyIndent, "self.sbe_rewind()");
        }

        for (int i = 0, size = groups.size(); i < size; i++)
        {
            final Token groupToken = groups.get(i);
            if (groupToken.signal() != Signal.BEGIN_GROUP)
            {
                throw new IllegalStateException("tokens must begin with BEGIN_GROUP: token=" + groupToken);
            }

            final String groupName = formatPropertyName(groupToken.name());
            final String groupDecoderName = decoderName(groupToken.name());

            append(sb, bodyIndent, groupName + ": " + groupDecoderName + " = self." + groupName + "()");
            append(sb, bodyIndent, "if " + groupName + ".count() > 0:");
            append(sb, bodyIndent, "    for _ in " + groupName + ":");
            append(sb, bodyIndent, "        " + groupName + ".sbe_skip()");
            i = findEndSignal(groups, i, Signal.END_GROUP, groupToken.name());
        }

        for (int i = 0, size = varData.size(); i < size;)
        {
            final Token varDataToken = varData.get(i);
            if (varDataToken.signal() != Signal.BEGIN_VAR_DATA)
            {
                throw new IllegalStateException("tokens must begin with BEGIN_VAR_DATA: token=" + varDataToken);
            }

            final String varDataName = formatPropertyName(varDataToken.name());
            append(sb, bodyIndent, "self.skip_" + varDataName + "()");

            i += varDataToken.componentTokenCount();
        }

        sb.append('\n');
        append(sb, bodyIndent, "return self");
    }

    private String encoderName(final String className)
    {
        return formatClassName(className) + "Encoder";
    }

    private String decoderName(final String className)
    {
        return formatClassName(className) + "Decoder";
    }

    private String implementsInterface(final String interfaceName)
    {
        return shouldGenerateInterfaces ? " implements " + interfaceName : "";
    }
}
