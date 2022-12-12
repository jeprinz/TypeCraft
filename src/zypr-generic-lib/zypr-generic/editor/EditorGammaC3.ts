import language from "../language/LanguageGamma";
import backend from "../backend/BackendC";
import frontend from "../frontend/Frontend3";

export default function editor() { return frontend(backend(language())) }