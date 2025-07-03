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

import static java.io.File.separatorChar;
import java.io.File;
import java.io.IOException;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Objects;
import org.agrona.generation.OutputManager;

/**
 * {@link OutputManager} for managing the creation of Python source files as the target of code generation.
 * The character encoding for the {@link Writer} is UTF-8.
 */
public class PythonOutputManager implements OutputManager
{
    private final File outputDir;

    /**
     * Create a new {@link OutputManager} for generating Python source files into a given package.
     *
     * @param baseDirName for the generated source code.
     * @param packageName for the generated source code relative to the baseDirName.
     */
    public PythonOutputManager(final String baseDirName, final String packageName)
    {
        Objects.requireNonNull(baseDirName, "baseDirName");
        Objects.requireNonNull(packageName, "packageName");

        final char lastChar = baseDirName.charAt(baseDirName.length() - 1);
        final String dirName = lastChar == separatorChar ? baseDirName : baseDirName + separatorChar;
        final String packageComponent = packageName.replace('.', '_');
        final String packageDirName = dirName + packageComponent;

        outputDir = new File(packageDirName);
        if (!outputDir.exists())
        {
            if (!outputDir.mkdirs())
            {
                throw new IllegalStateException("Unable to create directory: " + packageDirName);
            }
        }
    }

    /**
     * Create a new output which will be a Python source file in the given package.
     * <p>
     * The {@link Writer} should be closed once the caller has finished with it. The Writer is
     * buffered for efficient IO operations.
     *
     * @param name the name of the Python class.
     * @return a {@link Writer} to which the source code should be written.
     * @throws IOException if an issue occurs when creating the file.
     */
    public Writer createOutput(final String name) throws IOException
    {
        final File targetFile = new File(outputDir, name + ".py");

        return Files.newBufferedWriter(targetFile.toPath(), StandardCharsets.UTF_8);
    }
}
